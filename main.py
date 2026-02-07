# Installation:
#   python -m pip install requests shapely pyproj geopandas pandas numpy
# Run:
#   python main.py --bbox "minLon,minLat,maxLon,maxLat" --out_dir ./out
#   python main.py --aoi path.geojson --out_dir ./out

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
import threading
import time
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple

import numpy as np
import requests
from pyproj import CRS, Transformer
from shapely import geometry as geom
from shapely.ops import transform, unary_union
from shapely.validation import make_valid


OVERPASS_URL = os.environ.get("OVERPASS_URL", "https://overpass-api.de/api/interpreter")

PREFERRED_BUILDINGS = {
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

EXCLUDED_BUILDINGS = {"hut", "shed", "garage", "kiosk", "terrace", "cabin", "roof"}

RESIDENTIAL_BUILDINGS = {
    "residential",
    "house",
    "apartments",
    "detached",
    "semidetached_house",
    "terrace",
    "bungalow",
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

SOLAR_TAG_VALUES = {"solar", "photovoltaic", "yes", "true"}

ORIENTATION_MAP = {
    "N": 0,
    "NE": 45,
    "E": 90,
    "SE": 135,
    "S": 180,
    "SW": 225,
    "W": 270,
    "NW": 315,
}


@dataclass
class Config:
    aoi_path: Optional[str]
    bbox: Optional[Tuple[float, float, float, float]]
    min_area_m2: float
    target: str
    tile_size_deg: float
    max_candidates: int
    out_dir: str
    strict: bool
    workers: int
    timeout_s: int
    cache_dir: str
    seed: int


@dataclass
class TileResult:
    elements: List[Dict[str, Any]]
    failed: bool = False
    error: Optional[str] = None


@dataclass
class Metrics:
    area_m2: float
    perimeter_m: float
    compactness: float
    convexity: float
    rectangularity: float
    aspect_ratio: float
    vertex_count: int
    hole_area_ratio: float
    min_width_m: float


@dataclass
class Candidate:
    osm_id: str
    osm_type: str
    geometry: geom.base.BaseGeometry
    tags: Dict[str, Any]
    metrics: Metrics
    orientation_deg: Optional[float]
    orientation_confidence: str
    score: float
    solar_status: str
    centroid_lon: float
    centroid_lat: float


@dataclass
class Stats:
    total_elements: int = 0
    fetched_tiles: int = 0
    failed_tiles: int = 0
    discarded_invalid: int = 0
    discarded_solar: int = 0
    discarded_excluded_building: int = 0
    discarded_geometry_filter: Dict[str, int] = field(default_factory=dict)
    discarded_target: int = 0
    dedup_removed: int = 0
    start_time: float = field(default_factory=time.time)
    stage_times: Dict[str, float] = field(default_factory=dict)

    def inc_reason(self, key: str, count: int = 1) -> None:
        self.discarded_geometry_filter[key] = self.discarded_geometry_filter.get(key, 0) + count


class RateLimiter:
    def __init__(self, min_interval_s: float = 1.0) -> None:
        self.min_interval_s = min_interval_s
        self.lock = threading.Lock()
        self.last_call = 0.0

    def wait(self) -> None:
        with self.lock:
            now = time.time()
            elapsed = now - self.last_call
            if elapsed < self.min_interval_s:
                time.sleep(self.min_interval_s - elapsed)
            self.last_call = time.time()


class OverpassClient:
    def __init__(self, timeout_s: int, cache_dir: str, rate_limiter: RateLimiter) -> None:
        self.timeout_s = timeout_s
        self.cache_dir = cache_dir
        self.rate_limiter = rate_limiter
        os.makedirs(self.cache_dir, exist_ok=True)

    def _cache_path(self, query: str) -> str:
        digest = hashlib.md5(query.encode("utf-8")).hexdigest()
        return os.path.join(self.cache_dir, f"{digest}.json")

    def fetch(self, query: str) -> Dict[str, Any]:
        cache_path = self._cache_path(query)
        if os.path.exists(cache_path):
            with open(cache_path, "r", encoding="utf-8") as handle:
                return json.load(handle)

        backoff = 2.0
        for attempt in range(6):
            try:
                self.rate_limiter.wait()
                response = requests.post(
                    OVERPASS_URL,
                    data=query.encode("utf-8"),
                    timeout=self.timeout_s,
                    headers={"Content-Type": "application/x-www-form-urlencoded"},
                )
                if response.status_code in {429, 504}:
                    raise requests.HTTPError(f"{response.status_code} {response.text}")
                response.raise_for_status()
                payload = response.json()
                with open(cache_path, "w", encoding="utf-8") as handle:
                    json.dump(payload, handle)
                return payload
            except (requests.Timeout, requests.HTTPError, requests.ConnectionError) as exc:
                logging.warning("Overpass request failed (attempt %s): %s", attempt + 1, exc)
                if attempt == 5:
                    raise
                time.sleep(backoff)
                backoff *= 2
        raise RuntimeError("Overpass fetch failed after retries")


def parse_args() -> Config:
    parser = argparse.ArgumentParser(description="Roof candidate identification via OSM/Overpass")
    parser.add_argument("--aoi", dest="aoi_path", help="Path to AOI GeoJSON")
    parser.add_argument("--bbox", help="minLon,minLat,maxLon,maxLat")
    parser.add_argument("--min_area_m2", type=float, default=300)
    parser.add_argument("--target", choices=["commercial", "industrial", "mixed"], default="mixed")
    parser.add_argument("--tile_size_deg", type=float, default=0.01)
    parser.add_argument("--max_candidates", type=int, default=3000)
    parser.add_argument("--out_dir", default="./out")
    parser.add_argument("--strict", action="store_true")
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--timeout_s", type=int, default=180)
    parser.add_argument("--cache_dir", default="./.cache_overpass")
    parser.add_argument("--seed", type=int, default=42)

    args = parser.parse_args()

    bbox = None
    if args.bbox:
        try:
            parts = [float(p) for p in args.bbox.split(",")]
            if len(parts) != 4:
                raise ValueError
            bbox = (parts[0], parts[1], parts[2], parts[3])
        except ValueError:
            raise SystemExit("Invalid --bbox format. Use minLon,minLat,maxLon,maxLat")

    if not args.aoi_path and not bbox:
        raise SystemExit("Provide --aoi or --bbox")

    return Config(
        aoi_path=args.aoi_path,
        bbox=bbox,
        min_area_m2=args.min_area_m2,
        target=args.target,
        tile_size_deg=args.tile_size_deg,
        max_candidates=args.max_candidates,
        out_dir=args.out_dir,
        strict=args.strict,
        workers=args.workers,
        timeout_s=args.timeout_s,
        cache_dir=args.cache_dir,
        seed=args.seed,
    )


def load_aoi(config: Config) -> Tuple[geom.base.BaseGeometry, Tuple[float, float, float, float]]:
    if config.aoi_path:
        with open(config.aoi_path, "r", encoding="utf-8") as handle:
            data = json.load(handle)
        if data.get("type") == "FeatureCollection":
            shapes = [geom.shape(feature["geometry"]) for feature in data["features"]]
            polygon = unary_union(shapes)
        elif data.get("type") == "Feature":
            polygon = geom.shape(data["geometry"])
        else:
            polygon = geom.shape(data)
        polygon = polygon.buffer(0)
        return polygon, polygon.bounds
    min_lon, min_lat, max_lon, max_lat = config.bbox
    polygon = geom.box(min_lon, min_lat, max_lon, max_lat)
    return polygon, (min_lon, min_lat, max_lon, max_lat)


def tile_bounds(bounds: Tuple[float, float, float, float], tile_size_deg: float) -> List[Tuple[float, float, float, float]]:
    min_lon, min_lat, max_lon, max_lat = bounds
    tiles = []
    lon = min_lon
    while lon < max_lon:
        lat = min_lat
        next_lon = min(lon + tile_size_deg, max_lon)
        while lat < max_lat:
            next_lat = min(lat + tile_size_deg, max_lat)
            tiles.append((lon, lat, next_lon, next_lat))
            lat = next_lat
        lon = next_lon
    return tiles


def build_query(tile: Tuple[float, float, float, float], timeout_s: int) -> str:
    min_lon, min_lat, max_lon, max_lat = tile
    bbox = f"{min_lat},{min_lon},{max_lat},{max_lon}"
    query = (
        f"[out:json][timeout:{timeout_s}];("
        f"way[\"building\"]({bbox});"
        f"way[\"building:part\"]({bbox});"
        f"relation[\"building\"]({bbox});"
        f"relation[\"building:part\"]({bbox});" 
        f");out body geom;"
    )
    return query


def fetch_tile(client: OverpassClient, tile: Tuple[float, float, float, float], timeout_s: int) -> TileResult:
    query = build_query(tile, timeout_s)
    try:
        payload = client.fetch(query)
        elements = payload.get("elements", [])
        return TileResult(elements=elements)
    except Exception as exc:  # noqa: BLE001
        return TileResult(elements=[], failed=True, error=str(exc))


def sanitize_tags(tags: Dict[str, Any]) -> Dict[str, Any]:
    keep_keys = {
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
    for key in list(tags.keys()):
        if key.startswith("addr:"):
            keep_keys.add(key)
    return {k: tags.get(k) for k in keep_keys if k in tags}


def has_solar(tags: Dict[str, Any]) -> bool:
    for key, value in tags.items():
        if key in SOLAR_TAG_KEYS:
            if isinstance(value, str) and value.lower() in SOLAR_TAG_VALUES:
                return True
            if key in {"rooftop:solar", "roof:solar"}:
                return True
        if key in {"solar_panel", "solar_panels"} and str(value).lower() in SOLAR_TAG_VALUES:
            return True
    if tags.get("power") == "generator" and tags.get("generator:source") == "solar":
        return True
    return False


def element_to_geometry(element: Dict[str, Any]) -> Optional[geom.base.BaseGeometry]:
    if "geometry" in element:
        coords = [(p["lon"], p["lat"]) for p in element["geometry"]]
        if len(coords) < 3:
            return None
        if coords[0] != coords[-1]:
            coords.append(coords[0])
        return geom.Polygon(coords)
    if element.get("type") == "relation":
        members = element.get("members", [])
        outers = []
        inners = []
        for member in members:
            if "geometry" not in member:
                continue
            coords = [(p["lon"], p["lat"]) for p in member["geometry"]]
            if len(coords) < 3:
                continue
            if coords[0] != coords[-1]:
                coords.append(coords[0])
            ring = geom.LinearRing(coords)
            if member.get("role") == "inner":
                inners.append(ring)
            else:
                outers.append(ring)
        if not outers:
            return None
        polygons = []
        for outer in outers:
            inner_rings = [inner for inner in inners if inner.within(geom.Polygon(outer))]
            polygons.append(geom.Polygon(outer, inner_rings))
        if len(polygons) == 1:
            return polygons[0]
        return geom.MultiPolygon(polygons)
    return None


def get_utm_crs(lon: float, lat: float) -> CRS:
    zone = int((lon + 180) / 6) + 1
    epsg = 32600 + zone if lat >= 0 else 32700 + zone
    return CRS.from_epsg(epsg)


def project_geometry(geometry: geom.base.BaseGeometry) -> geom.base.BaseGeometry:
    centroid = geometry.centroid
    utm = get_utm_crs(centroid.x, centroid.y)
    transformer = Transformer.from_crs("EPSG:4326", utm, always_xy=True)
    return transform(transformer.transform, geometry)


def compute_metrics(geometry: geom.base.BaseGeometry) -> Optional[Metrics]:
    if geometry.is_empty:
        return None
    try:
        geometry = make_valid(geometry)
    except Exception:  # noqa: BLE001
        geometry = geometry.buffer(0)
    if not geometry.is_valid or geometry.is_empty:
        return None

    projected = project_geometry(geometry)
    if projected.is_empty:
        return None

    area = projected.area
    perimeter = projected.length
    if perimeter == 0:
        return None
    compactness = 4 * math.pi * area / (perimeter * perimeter)
    convex_hull = projected.convex_hull
    convexity = area / convex_hull.area if convex_hull.area else 0.0

    min_rect = projected.minimum_rotated_rectangle
    rect_area = min_rect.area if min_rect.area else 0.0
    rectangularity = area / rect_area if rect_area else 0.0

    coords = list(min_rect.exterior.coords)
    edges = [geom.LineString([coords[i], coords[i + 1]]) for i in range(4)]
    lengths = sorted([edge.length for edge in edges if edge.length > 0])
    if len(lengths) < 2:
        return None
    width, height = lengths[0], lengths[-1]
    aspect_ratio = height / width if width else 0.0

    vertex_count = len(projected.exterior.coords) if hasattr(projected, "exterior") else 0
    hole_area = 0.0
    if hasattr(projected, "interiors"):
        for ring in projected.interiors:
            hole_area += geom.Polygon(ring).area
    hole_area_ratio = hole_area / area if area else 0.0

    return Metrics(
        area_m2=area,
        perimeter_m=perimeter,
        compactness=compactness,
        convexity=convexity,
        rectangularity=rectangularity,
        aspect_ratio=aspect_ratio,
        vertex_count=vertex_count,
        hole_area_ratio=hole_area_ratio,
        min_width_m=width,
    )


def orientation_from_tags(tags: Dict[str, Any]) -> Tuple[Optional[float], str]:
    direction = tags.get("roof:direction")
    if direction is not None:
        try:
            return float(direction) % 360, "high"
        except ValueError:
            pass
    orientation = tags.get("roof:orientation")
    if orientation:
        orientation = orientation.upper()
        if orientation in ORIENTATION_MAP:
            return float(ORIENTATION_MAP[orientation]), "high"
    return None, "none"


def orientation_from_geometry(geometry: geom.base.BaseGeometry) -> Optional[float]:
    projected = project_geometry(geometry)
    min_rect = projected.minimum_rotated_rectangle
    coords = list(min_rect.exterior.coords)
    if len(coords) < 4:
        return None
    edge = geom.LineString([coords[0], coords[1]])
    dx = coords[1][0] - coords[0][0]
    dy = coords[1][1] - coords[0][1]
    if edge.length == 0:
        return None
    angle = math.degrees(math.atan2(dy, dx))
    angle = (angle + 360) % 180
    return angle


def orientation_score(angle: Optional[float], confidence: str) -> float:
    if angle is None:
        return 4.0
    north = angle >= 315 or angle <= 45
    south = 135 <= angle <= 225
    if confidence == "high":
        if north:
            return 10.0
        if south:
            return 2.0
        return 6.0
    if confidence == "low":
        if north:
            return 6.0
        if south:
            return 1.0
        return 4.0
    return 4.0


def geometry_score(metrics: Metrics) -> float:
    scores = []
    scores.append(np.clip(metrics.compactness / 0.4, 0, 1))
    scores.append(np.clip(metrics.convexity / 1.0, 0, 1))
    scores.append(np.clip(metrics.rectangularity / 1.0, 0, 1))
    aspect = np.clip((8 - metrics.aspect_ratio) / 8, 0, 1)
    scores.append(aspect)
    hole_score = np.clip((0.15 - metrics.hole_area_ratio) / 0.15, 0, 1)
    scores.append(hole_score)
    width_score = np.clip((metrics.min_width_m - 4) / 6, 0, 1)
    scores.append(width_score)
    return float(np.mean(scores) * 45)


def area_score(area_m2: float, base: float = 300, cap: float = 2000) -> float:
    if area_m2 <= base:
        return 0.0
    if area_m2 >= cap:
        return 40.0
    return float(((area_m2 - base) / (cap - base)) * 40)


def tag_confidence_score(tags: Dict[str, Any]) -> float:
    score = 0.0
    building = tags.get("building")
    if building in PREFERRED_BUILDINGS:
        score += 2.0
    if any(key.startswith("roof:") for key in tags.keys()):
        score += 3.0
    return score


def filter_metrics(metrics: Metrics, config: Config, stats: Stats) -> bool:
    strict = config.strict
    thresholds = {
        "area_m2": config.min_area_m2,
        "compactness": 0.20 if strict else 0.15,
        "convexity": 0.82 if strict else 0.75,
        "rectangularity": 0.70 if strict else 0.60,
        "aspect_ratio": 6 if strict else 8,
        "vertex_count": 60 if strict else 80,
        "hole_area_ratio": 0.08 if strict else 0.15,
        "min_width_m": 5 if strict else 4,
    }

    if metrics.area_m2 < thresholds["area_m2"]:
        stats.inc_reason("area_m2")
        return False
    if metrics.compactness < thresholds["compactness"]:
        stats.inc_reason("compactness")
        return False
    if metrics.convexity < thresholds["convexity"]:
        stats.inc_reason("convexity")
        return False
    if metrics.rectangularity < thresholds["rectangularity"]:
        stats.inc_reason("rectangularity")
        return False
    if metrics.aspect_ratio > thresholds["aspect_ratio"]:
        stats.inc_reason("aspect_ratio")
        return False
    if metrics.vertex_count > thresholds["vertex_count"]:
        stats.inc_reason("vertex_count")
        return False
    if metrics.hole_area_ratio > thresholds["hole_area_ratio"]:
        stats.inc_reason("hole_area_ratio")
        return False
    if metrics.min_width_m < thresholds["min_width_m"]:
        stats.inc_reason("min_width_m")
        return False
    return True


def matches_target(tags: Dict[str, Any], target: str) -> bool:
    building = tags.get("building") or ""
    if target == "mixed":
        return True
    if target == "industrial":
        return building in {"industrial", "warehouse"}
    if target == "commercial":
        return building in {"commercial", "retail", "supermarket", "office"}
    return True


def deduplicate(candidates: List[Candidate], stats: Stats) -> List[Candidate]:
    if not candidates:
        return []
    candidates_sorted = sorted(candidates, key=lambda c: c.score, reverse=True)
    kept: List[Candidate] = []
    for candidate in candidates_sorted:
        duplicate = False
        for kept_candidate in kept:
            inter = candidate.geometry.intersection(kept_candidate.geometry)
            if inter.is_empty:
                continue
            union = candidate.geometry.union(kept_candidate.geometry)
            iou = inter.area / union.area if union.area else 0.0
            if iou > 0.9:
                duplicate = True
                break
        if not duplicate:
            kept.append(candidate)
        else:
            stats.dedup_removed += 1

    resolved: List[Candidate] = []
    for candidate in kept:
        if candidate.tags.get("building:part"):
            resolved.append(candidate)
            continue
        overlap_parts = [
            other
            for other in kept
            if other.tags.get("building:part")
            and other.geometry.intersects(candidate.geometry)
        ]
        prefer_part = False
        for other in overlap_parts:
            inter = other.geometry.intersection(candidate.geometry)
            union = other.geometry.union(candidate.geometry)
            iou = inter.area / union.area if union.area else 0.0
            if iou > 0.8 and any(k.startswith("roof:") for k in other.tags):
                prefer_part = True
                break
        if prefer_part:
            stats.dedup_removed += 1
        else:
            resolved.append(candidate)
    return resolved


def to_feature(candidate: Candidate) -> Dict[str, Any]:
    return {
        "type": "Feature",
        "geometry": geom.mapping(candidate.geometry),
        "properties": {
            "osm_id": candidate.osm_id,
            "osm_type": candidate.osm_type,
            "building": candidate.tags.get("building"),
            "area_m2": round(candidate.metrics.area_m2, 2),
            "score": round(candidate.score, 2),
            "rectangularity": round(candidate.metrics.rectangularity, 3),
            "convexity": round(candidate.metrics.convexity, 3),
            "compactness": round(candidate.metrics.compactness, 3),
            "aspect_ratio": round(candidate.metrics.aspect_ratio, 3),
            "orientation_deg": round(candidate.orientation_deg, 1) if candidate.orientation_deg else None,
            "orientation_confidence": candidate.orientation_confidence,
            "solar_status": candidate.solar_status,
            "centroid_lat": round(candidate.centroid_lat, 6),
            "centroid_lon": round(candidate.centroid_lon, 6),
            "tags_relevantes": candidate.tags,
        },
    }


def export_outputs(candidates: List[Candidate], config: Config) -> None:
    os.makedirs(config.out_dir, exist_ok=True)
    features = [to_feature(candidate) for candidate in candidates]
    geojson = {"type": "FeatureCollection", "features": features}
    geojson_path = os.path.join(config.out_dir, "candidates.geojson")
    with open(geojson_path, "w", encoding="utf-8") as handle:
        json.dump(geojson, handle)

    csv_path = os.path.join(config.out_dir, "candidates.csv")
    with open(csv_path, "w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "osm_id",
                "osm_type",
                "building",
                "area_m2",
                "score",
                "rectangularity",
                "convexity",
                "compactness",
                "aspect_ratio",
                "orientation_deg",
                "orientation_confidence",
                "solar_status",
                "centroid_lat",
                "centroid_lon",
                "tags_relevantes",
            ],
        )
        writer.writeheader()
        for candidate in candidates:
            writer.writerow(
                {
                    "osm_id": candidate.osm_id,
                    "osm_type": candidate.osm_type,
                    "building": candidate.tags.get("building"),
                    "area_m2": round(candidate.metrics.area_m2, 2),
                    "score": round(candidate.score, 2),
                    "rectangularity": round(candidate.metrics.rectangularity, 3),
                    "convexity": round(candidate.metrics.convexity, 3),
                    "compactness": round(candidate.metrics.compactness, 3),
                    "aspect_ratio": round(candidate.metrics.aspect_ratio, 3),
                    "orientation_deg": round(candidate.orientation_deg, 1) if candidate.orientation_deg else None,
                    "orientation_confidence": candidate.orientation_confidence,
                    "solar_status": candidate.solar_status,
                    "centroid_lat": round(candidate.centroid_lat, 6),
                    "centroid_lon": round(candidate.centroid_lon, 6),
                    "tags_relevantes": json.dumps(candidate.tags, ensure_ascii=False),
                }
            )


def write_report(
    candidates: List[Candidate],
    config: Config,
    stats: Stats,
    failed_tiles: List[Tuple[float, float, float, float]],
) -> None:
    total_time = time.time() - stats.start_time
    total_elements = max(stats.total_elements, 1)

    def fmt_count(value: int) -> str:
        pct = (value / total_elements) * 100
        return f"{value} ({pct:.2f}%)"

    report_path = os.path.join(config.out_dir, "report.md")
    with open(report_path, "w", encoding="utf-8") as handle:
        handle.write("# Roof Candidate Report\n\n")
        handle.write("## Parameters\n")
        handle.write("```\n")
        handle.write(json.dumps(config.__dict__, indent=2, ensure_ascii=False))
        handle.write("\n```\n\n")
        handle.write("## Summary\n")
        handle.write(f"Total elements fetched: {stats.total_elements}\n\n")
        handle.write(f"Tiles fetched: {stats.fetched_tiles}\n\n")
        handle.write(f"Tiles failed: {stats.failed_tiles}\n\n")
        handle.write(f"Discarded invalid geometry: {fmt_count(stats.discarded_invalid)}\n\n")
        handle.write(f"Discarded solar tags: {fmt_count(stats.discarded_solar)}\n\n")
        handle.write(
            f"Discarded excluded building: {fmt_count(stats.discarded_excluded_building)}\n\n"
        )
        handle.write(f"Discarded target mismatch: {fmt_count(stats.discarded_target)}\n\n")
        handle.write(f"Deduplicated removed: {fmt_count(stats.dedup_removed)}\n\n")
        handle.write("### Geometry filter removals\n")
        for reason, count in stats.discarded_geometry_filter.items():
            handle.write(f"- {reason}: {fmt_count(count)}\n")
        handle.write("\n")
        handle.write("## Timing\n")
        for stage, duration in stats.stage_times.items():
            handle.write(f"- {stage}: {duration:.2f}s\n")
        handle.write(f"- total: {total_time:.2f}s\n\n")

        if failed_tiles:
            handle.write("## Failed tiles\n")
            for tile in failed_tiles:
                handle.write(f"- {tile}\n")
            handle.write("\n")

        handle.write("## Top 50 candidates\n")
        handle.write("| osm_id | score | area_m2 | building | orientation |\n")
        handle.write("| --- | --- | --- | --- | --- |\n")
        for candidate in candidates[:50]:
            orientation = (
                f"{candidate.orientation_deg:.1f} ({candidate.orientation_confidence})"
                if candidate.orientation_deg is not None
                else "None"
            )
            handle.write(
                f"| {candidate.osm_id} | {candidate.score:.2f} | {candidate.metrics.area_m2:.1f} | "
                f"{candidate.tags.get('building')} | {orientation} |\n"
            )


def process_elements(
    elements: List[Dict[str, Any]],
    aoi_polygon: geom.base.BaseGeometry,
    config: Config,
    stats: Stats,
) -> List[Candidate]:
    candidates: List[Candidate] = []
    for element in elements:
        stats.total_elements += 1
        tags = element.get("tags", {})
        if has_solar(tags):
            stats.discarded_solar += 1
            continue
        building = tags.get("building")
        if building and building in EXCLUDED_BUILDINGS:
            stats.discarded_excluded_building += 1
            continue
        if not matches_target(tags, config.target):
            stats.discarded_target += 1
            continue

        geometry = element_to_geometry(element)
        if geometry is None or geometry.is_empty:
            stats.discarded_invalid += 1
            continue
        if not geometry.intersects(aoi_polygon):
            continue
        metrics = compute_metrics(geometry)
        if not metrics:
            stats.discarded_invalid += 1
            continue
        if not filter_metrics(metrics, config, stats):
            continue

        tags_relevant = sanitize_tags(tags)
        orientation_deg, orientation_confidence = orientation_from_tags(tags_relevant)
        if orientation_deg is None:
            estimated = orientation_from_geometry(geometry)
            if estimated is not None:
                orientation_deg = estimated
                orientation_confidence = "low"

        area_component = area_score(metrics.area_m2)
        geometry_component = geometry_score(metrics)
        orientation_component = orientation_score(orientation_deg, orientation_confidence)
        tag_component = tag_confidence_score(tags_relevant)
        score = area_component + geometry_component + orientation_component + tag_component

        if building in RESIDENTIAL_BUILDINGS and metrics.area_m2 < 600:
            score -= 15

        centroid = geometry.centroid
        candidate = Candidate(
            osm_id=f"{element.get('type')}:{element.get('id')}",
            osm_type=element.get("type"),
            geometry=geometry,
            tags=tags_relevant,
            metrics=metrics,
            orientation_deg=orientation_deg,
            orientation_confidence=orientation_confidence,
            score=score,
            solar_status="unknown",
            centroid_lon=centroid.x,
            centroid_lat=centroid.y,
        )
        candidates.append(candidate)
    return candidates


def main() -> None:
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s [%(levelname)s] %(message)s",
    )
    config = parse_args()
    random.seed(config.seed)

    aoi_polygon, bounds = load_aoi(config)

    if config.tile_size_deg <= 0:
        raise SystemExit("tile_size_deg must be > 0")

    tile_size = config.tile_size_deg
    tiles = tile_bounds(bounds, tile_size)
    if len(tiles) > 8000:
        scale = math.sqrt(len(tiles) / 8000)
        tile_size = round(tile_size * scale, 5)
        tiles = tile_bounds(bounds, tile_size)
        logging.warning(
            "Large tile count detected (%s). Adjusting tile_size_deg to %s.",
            len(tiles),
            tile_size,
        )
    elif len(tiles) > 5000:
        logging.warning("Large tile count detected: %s", len(tiles))

    client = OverpassClient(config.timeout_s, config.cache_dir, RateLimiter())

    stats = Stats()
    tile_results: List[TileResult] = []
    failed_tiles: List[Tuple[float, float, float, float]] = []

    start = time.time()
    with concurrent.futures.ThreadPoolExecutor(max_workers=config.workers) as executor:
        futures = {
            executor.submit(fetch_tile, client, tile, config.timeout_s): tile for tile in tiles
        }
        for future in concurrent.futures.as_completed(futures):
            tile = futures[future]
            result = future.result()
            tile_results.append(result)
            stats.fetched_tiles += 1
            if result.failed:
                stats.failed_tiles += 1
                failed_tiles.append(tile)
                logging.warning("Tile failed %s: %s", tile, result.error)
    stats.stage_times["fetch_tiles"] = time.time() - start

    all_elements = [element for result in tile_results for element in result.elements]
    if not all_elements:
        logging.warning("No elements fetched from Overpass")

    start = time.time()
    candidates = process_elements(all_elements, aoi_polygon, config, stats)
    stats.stage_times["process_elements"] = time.time() - start

    start = time.time()
    candidates = deduplicate(candidates, stats)
    stats.stage_times["deduplicate"] = time.time() - start

    candidates = sorted(candidates, key=lambda c: c.score, reverse=True)[: config.max_candidates]

    export_outputs(candidates, config)
    write_report(candidates, config, stats, failed_tiles)
    logging.info("Generated %s candidates", len(candidates))


if __name__ == "__main__":
    main()
