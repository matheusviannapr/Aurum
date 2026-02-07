#!/usr/bin/env python3
"""main.py
# Instalação:
#   python3 -m venv .venv && source .venv/bin/activate
#   pip install requests shapely pyproj geopandas pandas numpy
# Execução:
#   python main.py --bbox "minLon,minLat,maxLon,maxLat" --out_dir ./out
"""

from __future__ import annotations

import argparse
import concurrent.futures
import csv
import hashlib
import json
import logging
import math
import os
import random
import sys
import threading
import time
from collections import Counter, defaultdict
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple

import numpy as np
import pandas as pd
import requests
from shapely.geometry import MultiPolygon, Polygon, box, shape
from shapely.ops import polygonize, transform
from shapely.strtree import STRtree
from shapely.validation import make_valid
from pyproj import CRS, Transformer
import geopandas as gpd

OVERPASS_URL = "https://overpass-api.de/api/interpreter"

PRIORITY_BUILDINGS = {
    "industrial",
    "warehouse",
    "commercial",
    "retail",
    "supermarket",
    "office",
    "school",
    "university",
    "hospital",
}

EXCLUDE_BUILDINGS = {
    "hut",
    "shed",
    "garage",
    "kiosk",
    "terrace",
    "cabin",
    "roof",
}

RESIDENTIAL_BUILDINGS = {
    "house",
    "residential",
    "apartments",
    "detached",
    "semidetached_house",
    "terrace",
    "bungalow",
    "hut",
}

SOLAR_TAG_KEYS = {
    "generator:source",
    "generator:method",
    "power",
    "solar_panel",
    "solar_panels",
    "rooftop:solar",
    "roof:solar",
}

RELEVANT_TAG_KEYS = {
    "building",
    "building:part",
    "name",
    "roof:shape",
    "roof:direction",
    "roof:orientation",
    "roof:material",
    "building:levels",
    "height",
}

ORIENTATION_MAP = {
    "N": 0,
    "NNE": 22.5,
    "NE": 45,
    "ENE": 67.5,
    "E": 90,
    "ESE": 112.5,
    "SE": 135,
    "SSE": 157.5,
    "S": 180,
    "SSW": 202.5,
    "SW": 225,
    "WSW": 247.5,
    "W": 270,
    "WNW": 292.5,
    "NW": 315,
    "NNW": 337.5,
}


@dataclass
class Candidate:
    osm_id: str
    osm_type: str
    geometry: Polygon
    tags: Dict[str, Any]
    area_m2: float
    perimeter_m: float
    compactness: float
    convexity: float
    rectangularity: float
    aspect_ratio: float
    vertex_count: int
    hole_area_ratio: float
    min_width_m: float
    orientation_deg: Optional[float]
    orientation_confidence: str
    solar_status: str
    centroid_lat: float
    centroid_lon: float
    score: float


class RateLimiter:
    def __init__(self, min_interval_s: float = 1.0) -> None:
        self.min_interval_s = min_interval_s
        self.lock = threading.Lock()
        self.last_time = 0.0

    def wait(self) -> None:
        with self.lock:
            now = time.time()
            elapsed = now - self.last_time
            if elapsed < self.min_interval_s:
                time.sleep(self.min_interval_s - elapsed)
            self.last_time = time.time()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Identify rooftop candidates from OSM/Overpass")
    parser.add_argument("--aoi", type=str, help="Path to AOI geojson")
    parser.add_argument("--bbox", type=str, help='"minLon,minLat,maxLon,maxLat"')
    parser.add_argument("--min_area_m2", type=float, default=300)
    parser.add_argument("--target", type=str, choices=["commercial", "industrial", "mixed"], default="mixed")
    parser.add_argument("--tile_size_deg", type=float, default=0.01)
    parser.add_argument("--max_candidates", type=int, default=3000)
    parser.add_argument("--out_dir", type=str, default="./out")
    parser.add_argument("--strict", action="store_true")
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--timeout_s", type=int, default=180)
    parser.add_argument("--cache_dir", type=str, default="./.cache_overpass")
    parser.add_argument("--seed", type=int, default=42)
    return parser.parse_args()


def load_aoi_geometry(args: argparse.Namespace) -> Polygon:
    if args.aoi:
        gdf = gpd.read_file(args.aoi)
        geom = gdf.geometry.unary_union
        if isinstance(geom, MultiPolygon):
            geom = max(geom.geoms, key=lambda g: g.area)
        if not isinstance(geom, Polygon):
            raise ValueError("AOI geometry must be polygonal")
        return geom
    if args.bbox:
        parts = [float(x.strip()) for x in args.bbox.split(",")]
        if len(parts) != 4:
            raise ValueError("bbox must have 4 comma-separated values")
        min_lon, min_lat, max_lon, max_lat = parts
        return box(min_lon, min_lat, max_lon, max_lat)
    raise ValueError("Either --aoi or --bbox must be provided")


def build_tiles(aoi: Polygon, tile_size_deg: float) -> List[Polygon]:
    minx, miny, maxx, maxy = aoi.bounds
    tiles: List[Polygon] = []
    x = minx
    while x < maxx:
        y = miny
        while y < maxy:
            tile = box(x, y, min(x + tile_size_deg, maxx), min(y + tile_size_deg, maxy))
            if tile.intersects(aoi):
                tiles.append(tile)
            y += tile_size_deg
        x += tile_size_deg
    return tiles


def adapt_tile_size(aoi: Polygon, tile_size_deg: float) -> float:
    tiles = build_tiles(aoi, tile_size_deg)
    if len(tiles) <= 2000:
        return tile_size_deg
    factor = math.sqrt(len(tiles) / 2000)
    return tile_size_deg * factor


def build_query(tile: Polygon, timeout_s: int) -> str:
    minx, miny, maxx, maxy = tile.bounds
    return (
        f"[out:json][timeout:{timeout_s}];("
        f"way[\"building\"]({miny},{minx},{maxy},{maxx});"
        f"relation[\"building\"]({miny},{minx},{maxy},{maxx});"
        f"way[\"building:part\"]({miny},{minx},{maxy},{maxx});"
        f"relation[\"building:part\"]({miny},{minx},{maxy},{maxx});"
        ");out body geom;"
    )


def query_overpass(
    query: str,
    cache_dir: Path,
    rate_limiter: RateLimiter,
    timeout_s: int,
) -> Dict[str, Any]:
    cache_dir.mkdir(parents=True, exist_ok=True)
    q_hash = hashlib.md5(query.encode("utf-8")).hexdigest()
    cache_file = cache_dir / f"{q_hash}.json"
    if cache_file.exists():
        with cache_file.open("r", encoding="utf-8") as f:
            return json.load(f)

    backoff = 2
    for attempt in range(5):
        try:
            rate_limiter.wait()
            response = requests.post(OVERPASS_URL, data=query, timeout=timeout_s)
            if response.status_code in {429, 504}:
                raise requests.HTTPError(f"{response.status_code} rate limit")
            response.raise_for_status()
            data = response.json()
            with cache_file.open("w", encoding="utf-8") as f:
                json.dump(data, f)
            return data
        except (requests.Timeout, requests.HTTPError, requests.ConnectionError) as exc:
            logging.warning("Overpass error (attempt %s): %s", attempt + 1, exc)
            time.sleep(backoff)
            backoff *= 2
    raise RuntimeError("Overpass failed after retries")


def has_solar_tags(tags: Dict[str, Any]) -> bool:
    for key, value in tags.items():
        key_lower = key.lower()
        if key_lower in SOLAR_TAG_KEYS:
            if key_lower == "generator:source" and str(value).lower() == "solar":
                return True
            if key_lower == "generator:method" and str(value).lower() == "photovoltaic":
                return True
            if key_lower == "power" and str(value).lower() == "generator" and str(tags.get("generator:source", "")).lower() == "solar":
                return True
            if key_lower in {"solar_panel", "solar_panels"} and str(value).lower() in {"yes", "true", "1"}:
                return True
            if key_lower in {"rooftop:solar", "roof:solar"}:
                return True
    return False


def parse_way_geometry(geom_list: List[Dict[str, float]]) -> Optional[Polygon]:
    if not geom_list:
        return None
    coords = [(pt["lon"], pt["lat"]) for pt in geom_list]
    if len(coords) < 4:
        return None
    if coords[0] != coords[-1]:
        coords.append(coords[0])
    return Polygon(coords)


def parse_relation_geometry(members: List[Dict[str, Any]]) -> Optional[Polygon]:
    outer_lines = []
    inner_lines = []
    for member in members:
        if member.get("type") != "way" or "geometry" not in member:
            continue
        coords = [(pt["lon"], pt["lat"]) for pt in member["geometry"]]
        if len(coords) < 4:
            continue
        if member.get("role") == "inner":
            inner_lines.append(coords)
        else:
            outer_lines.append(coords)
    if not outer_lines:
        return None
    outer_polys = list(polygonize(outer_lines))
    if not outer_polys:
        return None
    if inner_lines:
        inners = list(polygonize(inner_lines))
        if inners:
            holes = [poly.exterior.coords[:] for poly in inners]
            poly = Polygon(outer_polys[0].exterior.coords, holes=holes)
            return poly
    return outer_polys[0]


def collect_elements(data: Dict[str, Any]) -> List[Tuple[str, str, Dict[str, Any], Polygon]]:
    elements = []
    for el in data.get("elements", []):
        tags = el.get("tags", {})
        if not tags:
            continue
        osm_type = el.get("type")
        osm_id = str(el.get("id"))
        geom = None
        if osm_type == "way":
            geom = parse_way_geometry(el.get("geometry", []))
        elif osm_type == "relation":
            geom = parse_relation_geometry(el.get("members", []))
        if geom is None:
            continue
        elements.append((osm_id, osm_type, tags, geom))
    return elements


def is_building_candidate(tags: Dict[str, Any]) -> bool:
    building = tags.get("building") or tags.get("building:part")
    if not building:
        return False
    building = str(building).lower()
    if building in EXCLUDE_BUILDINGS:
        return False
    if building in PRIORITY_BUILDINGS:
        return True
    if building == "yes":
        return True
    return True


def tags_subset(tags: Dict[str, Any]) -> Dict[str, Any]:
    subset = {k: v for k, v in tags.items() if k in RELEVANT_TAG_KEYS or k.startswith("addr:")}
    building = tags.get("building")
    if building:
        subset["building"] = building
    building_part = tags.get("building:part")
    if building_part:
        subset["building:part"] = building_part
    return subset


def utm_crs_for_lon_lat(lon: float, lat: float) -> CRS:
    zone = int((lon + 180) / 6) + 1
    if lat >= 0:
        return CRS.from_epsg(32600 + zone)
    return CRS.from_epsg(32700 + zone)


def compute_metrics(geom: Polygon) -> Optional[Dict[str, float]]:
    if geom.is_empty:
        return None
    geom = make_valid(geom)
    if geom.is_empty or not geom.is_valid:
        return None
    if isinstance(geom, MultiPolygon):
        geom = max(geom.geoms, key=lambda g: g.area)
    centroid = geom.centroid
    transformer = Transformer.from_crs("EPSG:4326", utm_crs_for_lon_lat(centroid.x, centroid.y), always_xy=True)
    geom_m = transform(transformer.transform, geom)
    if geom_m.is_empty or not geom_m.is_valid:
        return None
    area = geom_m.area
    perimeter = geom_m.length
    if perimeter == 0:
        return None
    compactness = 4 * math.pi * area / (perimeter**2)
    convex_area = geom_m.convex_hull.area
    convexity = area / convex_area if convex_area else 0
    min_rect = geom_m.minimum_rotated_rectangle
    rect_area = min_rect.area
    rectangularity = area / rect_area if rect_area else 0
    rect_coords = list(min_rect.exterior.coords)
    if len(rect_coords) < 4:
        return None
    edge_lengths = [
        math.dist(rect_coords[i], rect_coords[i + 1]) for i in range(len(rect_coords) - 1)
    ]
    edge_lengths = sorted(edge_lengths, reverse=True)
    length = edge_lengths[0]
    width = edge_lengths[1] if len(edge_lengths) > 1 else edge_lengths[0]
    aspect_ratio = length / width if width else 0
    vertex_count = len(geom_m.exterior.coords)
    hole_area = sum(Polygon(ring).area for ring in geom_m.interiors)
    hole_area_ratio = hole_area / area if area else 0
    min_width = min(length, width)
    return {
        "area_m2": area,
        "perimeter_m": perimeter,
        "compactness": compactness,
        "convexity": convexity,
        "rectangularity": rectangularity,
        "aspect_ratio": aspect_ratio,
        "vertex_count": vertex_count,
        "hole_area_ratio": hole_area_ratio,
        "min_width_m": min_width,
        "centroid_lat": centroid.y,
        "centroid_lon": centroid.x,
    }


def filter_geometry(metrics: Dict[str, float], min_area_m2: float, strict: bool) -> Optional[str]:
    thresholds = {
        "compactness": 0.20 if strict else 0.15,
        "convexity": 0.82 if strict else 0.75,
        "rectangularity": 0.70 if strict else 0.60,
        "aspect_ratio": 6 if strict else 8,
        "vertex_count": 60 if strict else 80,
        "hole_area_ratio": 0.08 if strict else 0.15,
        "min_width_m": 5 if strict else 4,
    }
    if metrics["area_m2"] < min_area_m2:
        return "area_m2"
    if metrics["compactness"] < thresholds["compactness"]:
        return "compactness"
    if metrics["convexity"] < thresholds["convexity"]:
        return "convexity"
    if metrics["rectangularity"] < thresholds["rectangularity"]:
        return "rectangularity"
    if metrics["aspect_ratio"] > thresholds["aspect_ratio"]:
        return "aspect_ratio"
    if metrics["vertex_count"] > thresholds["vertex_count"]:
        return "vertex_count"
    if metrics["hole_area_ratio"] > thresholds["hole_area_ratio"]:
        return "hole_area_ratio"
    if metrics["min_width_m"] < thresholds["min_width_m"]:
        return "min_width_m"
    return None


def orientation_from_tags(tags: Dict[str, Any]) -> Tuple[Optional[float], str]:
    if "roof:direction" in tags:
        try:
            return float(tags["roof:direction"]) % 360, "high"
        except ValueError:
            return None, "none"
    if "roof:orientation" in tags:
        value = str(tags["roof:orientation"]).upper()
        if value in ORIENTATION_MAP:
            return ORIENTATION_MAP[value], "high"
    return None, "none"


def estimate_orientation(geom: Polygon) -> Optional[float]:
    min_rect = geom.minimum_rotated_rectangle
    coords = list(min_rect.exterior.coords)
    if len(coords) < 4:
        return None
    p1, p2 = coords[0], coords[1]
    p3 = coords[1]
    p4 = coords[2]
    d1 = math.dist(p1, p2)
    d2 = math.dist(p3, p4)
    if d1 >= d2:
        dx = p2[0] - p1[0]
        dy = p2[1] - p1[1]
    else:
        dx = p4[0] - p3[0]
        dy = p4[1] - p3[1]
    if dx == 0 and dy == 0:
        return None
    angle = (math.degrees(math.atan2(dx, dy)) + 360) % 360
    return angle


def orientation_score(orientation: Optional[float], confidence: str) -> float:
    if orientation is None:
        return 0.0
    north = (orientation >= 315 or orientation <= 45)
    south = 135 <= orientation <= 225
    if confidence == "high":
        if north:
            return 10.0
        if south:
            return -6.0
        return 0.0
    if confidence == "low":
        if north:
            return 5.0
        if south:
            return -3.0
    return 0.0


def geometry_score(metrics: Dict[str, float]) -> float:
    comp = min(metrics["compactness"] / 0.3, 1.0)
    conv = min(metrics["convexity"] / 0.9, 1.0)
    rect = min(metrics["rectangularity"] / 0.9, 1.0)
    aspect = 1.0 - min(max(metrics["aspect_ratio"] - 2, 0) / 6, 1.0)
    holes = 1.0 - min(metrics["hole_area_ratio"] / 0.2, 1.0)
    score = np.mean([comp, conv, rect, aspect, holes])
    return float(score * 45)


def area_score(area: float, min_area: float = 300, max_area: float = 2000) -> float:
    if area <= min_area:
        return 0.0
    if area >= max_area:
        return 40.0
    return (area - min_area) / (max_area - min_area) * 40


def tag_confidence_score(tags: Dict[str, Any]) -> float:
    if any(k in tags for k in {"roof:shape", "roof:direction", "roof:orientation", "roof:material"}):
        return 5.0
    if tags.get("building") in PRIORITY_BUILDINGS:
        return 3.0
    return 0.0


def compute_score(metrics: Dict[str, float], tags: Dict[str, Any], orientation: Optional[float], confidence: str) -> float:
    score = area_score(metrics["area_m2"]) + geometry_score(metrics) + orientation_score(orientation, confidence)
    score += tag_confidence_score(tags)
    building = str(tags.get("building", "")).lower()
    if building in RESIDENTIAL_BUILDINGS and metrics["area_m2"] < 600:
        score -= 15.0
    return max(0.0, min(100.0, score))


def deduplicate_candidates(candidates: List[Candidate]) -> List[Candidate]:
    if not candidates:
        return []
    geoms = [c.geometry for c in candidates]
    tree = STRtree(geoms)
    to_remove = set()
    for idx, cand in enumerate(candidates):
        if idx in to_remove:
            continue
        matches = tree.query(cand.geometry)
        for geom in matches:
            jdx = geoms.index(geom)
            if jdx == idx or jdx in to_remove:
                continue
            other = candidates[jdx]
            inter = cand.geometry.intersection(other.geometry)
            if inter.is_empty:
                continue
            union_area = cand.geometry.union(other.geometry).area
            if union_area == 0:
                continue
            iou = inter.area / union_area
            if iou > 0.9:
                if other.score > cand.score:
                    to_remove.add(idx)
                else:
                    to_remove.add(jdx)
    return [c for idx, c in enumerate(candidates) if idx not in to_remove]


def prefer_building_parts(candidates: List[Candidate]) -> List[Candidate]:
    parts = [c for c in candidates if "building:part" in c.tags]
    buildings = [c for c in candidates if "building:part" not in c.tags]
    if not parts or not buildings:
        return candidates
    to_remove = set()
    building_geoms = [c.geometry for c in buildings]
    tree = STRtree(building_geoms)
    for part in parts:
        for geom in tree.query(part.geometry):
            idx = building_geoms.index(geom)
            building = buildings[idx]
            inter = part.geometry.intersection(building.geometry)
            if inter.is_empty:
                continue
            iou = inter.area / building.geometry.area if building.geometry.area else 0
            if iou > 0.8 and any(k.startswith("roof:") for k in part.tags):
                to_remove.add(building.osm_id)
    return [c for c in candidates if c.osm_id not in to_remove]


def process_tile(
    tile: Polygon,
    cache_dir: Path,
    rate_limiter: RateLimiter,
    timeout_s: int,
    min_area_m2: float,
    strict: bool,
    stats: Counter,
) -> List[Candidate]:
    query = build_query(tile, timeout_s)
    data = query_overpass(query, cache_dir, rate_limiter, timeout_s)
    elements = collect_elements(data)
    candidates: List[Candidate] = []
    for osm_id, osm_type, tags, geom in elements:
        if has_solar_tags(tags):
            stats["excluded_solar"] += 1
            continue
        if not is_building_candidate(tags):
            stats["excluded_building"] += 1
            continue
        metrics = compute_metrics(geom)
        if metrics is None:
            stats["invalid_geometry"] += 1
            continue
        reason = filter_geometry(metrics, min_area_m2, strict)
        if reason:
            stats[f"filtered_{reason}"] += 1
            continue
        orientation, confidence = orientation_from_tags(tags)
        if orientation is None:
            orientation = estimate_orientation(geom)
            confidence = "low" if orientation is not None else "none"
        score = compute_score(metrics, tags, orientation, confidence)
        solar_status = "unknown"
        candidate = Candidate(
            osm_id=osm_id,
            osm_type=osm_type,
            geometry=geom,
            tags=tags_subset(tags),
            area_m2=metrics["area_m2"],
            perimeter_m=metrics["perimeter_m"],
            compactness=metrics["compactness"],
            convexity=metrics["convexity"],
            rectangularity=metrics["rectangularity"],
            aspect_ratio=metrics["aspect_ratio"],
            vertex_count=metrics["vertex_count"],
            hole_area_ratio=metrics["hole_area_ratio"],
            min_width_m=metrics["min_width_m"],
            orientation_deg=orientation,
            orientation_confidence=confidence,
            solar_status=solar_status,
            centroid_lat=metrics["centroid_lat"],
            centroid_lon=metrics["centroid_lon"],
            score=score,
        )
        candidates.append(candidate)
        stats["candidates_kept"] += 1
    return candidates


def generate_report(
    out_dir: Path,
    args: argparse.Namespace,
    stats: Counter,
    timings: Dict[str, float],
    failures: List[str],
    top_candidates: List[Candidate],
) -> None:
    report_path = out_dir / "report.md"
    with report_path.open("w", encoding="utf-8") as f:
        f.write(f"# Report ({datetime.utcnow().isoformat()}Z)\n\n")
        f.write("## Parameters\n")
        for key, value in vars(args).items():
            f.write(f"- **{key}**: {value}\n")
        f.write("\n## Counts\n")
        total_removed = sum(v for k, v in stats.items() if k.startswith("filtered_") or k.startswith("excluded_"))
        total_kept = stats.get("candidates_kept", 0)
        total = total_removed + total_kept
        f.write(f"- Total processed: {total}\n")
        for key, value in stats.most_common():
            percent = (value / total * 100) if total else 0
            f.write(f"- {key}: {value} ({percent:.1f}%)\n")
        f.write("\n## Timings\n")
        for key, value in timings.items():
            f.write(f"- {key}: {value:.2f}s\n")
        if failures:
            f.write("\n## Tile Failures\n")
            for failure in failures:
                f.write(f"- {failure}\n")
        f.write("\n## Top 50\n")
        f.write("| osm_id | score | area_m2 | building | orientation |\n")
        f.write("| --- | --- | --- | --- | --- |\n")
        for cand in top_candidates[:50]:
            building = cand.tags.get("building") or cand.tags.get("building:part") or ""
            f.write(
                f"| {cand.osm_id} | {cand.score:.1f} | {cand.area_m2:.1f} | {building} | {cand.orientation_deg if cand.orientation_deg is not None else ''} |\n"
            )


def export_outputs(out_dir: Path, candidates: List[Candidate]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    records = []
    for cand in candidates:
        records.append(
            {
                "osm_id": cand.osm_id,
                "osm_type": cand.osm_type,
                "building": cand.tags.get("building") or cand.tags.get("building:part"),
                "area_m2": cand.area_m2,
                "score": cand.score,
                "rectangularity": cand.rectangularity,
                "convexity": cand.convexity,
                "compactness": cand.compactness,
                "aspect_ratio": cand.aspect_ratio,
                "orientation_deg": cand.orientation_deg,
                "orientation_confidence": cand.orientation_confidence,
                "solar_status": cand.solar_status,
                "centroid_lat": cand.centroid_lat,
                "centroid_lon": cand.centroid_lon,
                "tags_relevantes": json.dumps(cand.tags, ensure_ascii=False),
                "geometry": cand.geometry,
            }
        )
    gdf = gpd.GeoDataFrame(records, geometry="geometry", crs="EPSG:4326")
    gdf.to_file(out_dir / "candidates.geojson", driver="GeoJSON")
    df = pd.DataFrame(records).drop(columns=["geometry"])
    df.to_csv(out_dir / "candidates.csv", index=False)


def main() -> None:
    args = parse_args()
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
    random.seed(args.seed)
    np.random.seed(args.seed)

    start_time = time.time()
    aoi = load_aoi_geometry(args)
    tile_size = adapt_tile_size(aoi, args.tile_size_deg)
    tiles = build_tiles(aoi, tile_size)
    logging.info("Using %s tiles with size %.4f deg", len(tiles), tile_size)

    rate_limiter = RateLimiter(min_interval_s=1.0)
    stats: Counter = Counter()
    failures: List[str] = []
    cache_dir = Path(args.cache_dir)

    tile_start = time.time()
    candidates: List[Candidate] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as executor:
        futures = {
            executor.submit(
                process_tile,
                tile,
                cache_dir,
                rate_limiter,
                args.timeout_s,
                args.min_area_m2,
                args.strict,
                stats,
            ): tile
            for tile in tiles
        }
        for future in concurrent.futures.as_completed(futures):
            tile = futures[future]
            try:
                candidates.extend(future.result())
            except Exception as exc:  # noqa: BLE001
                logging.warning("Tile failed %s: %s", tile.bounds, exc)
                failures.append(str(tile.bounds))
    tile_time = time.time() - tile_start

    dedup_start = time.time()
    candidates = prefer_building_parts(candidates)
    candidates = deduplicate_candidates(candidates)
    dedup_time = time.time() - dedup_start

    candidates.sort(key=lambda c: c.score, reverse=True)
    candidates = candidates[: args.max_candidates]

    export_start = time.time()
    out_dir = Path(args.out_dir)
    export_outputs(out_dir, candidates)
    export_time = time.time() - export_start

    timings = {
        "total": time.time() - start_time,
        "tiles": tile_time,
        "dedup": dedup_time,
        "export": export_time,
    }
    generate_report(out_dir, args, stats, timings, failures, candidates)


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:  # noqa: BLE001
        logging.error("Fatal error: %s", exc)
        sys.exit(1)
