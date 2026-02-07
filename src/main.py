"""CLI for roof lead extraction."""
from __future__ import annotations

import argparse
import json
import logging
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from typing import Dict, List

from shapely.geometry import Polygon

from .export import ensure_output_dir, export_csv, export_geojson, export_report
from .filters import (
    FilterConfig,
    building_type,
    deduplicate,
    geometry_filter,
    is_excluded_building,
    is_priority_building,
    solar_status,
)
from .geom_metrics import compute_metrics, normalize_geometry, project_to_utm
from .orientation import compute_orientation
from .osm_parse import parse_elements
from .overpass import OverpassClient, OverpassConfig
from .scoring import final_score, pre_score
from .tiling import load_aoi, tile_bboxes


@dataclass
class PipelineConfig:
    min_area_m2: float
    target: str
    max_candidates: int
    tile_size_deg: float
    out_dir: str
    seed: int
    strict: bool


def setup_logging() -> None:
    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")


def target_allowed(tags: Dict[str, str], target: str) -> bool:
    if target == "mixed":
        return True
    if target == "industrial":
        return building_type(tags) in {"industrial", "warehouse"}
    if target == "commercial":
        return building_type(tags) in {
            "commercial",
            "retail",
            "supermarket",
            "office",
            "school",
            "university",
            "hospital",
        }
    return True


def prefer_parts(candidates: List[Dict]) -> List[Dict]:
    buildings = [c for c in candidates if c.get("tags", {}).get("building")]
    parts = [c for c in candidates if c.get("tags", {}).get("building:part")]
    filtered = []
    for building in buildings:
        keep = True
        for part in parts:
            if building["geometry"].area == 0:
                continue
            overlap = part["geometry"].intersection(building["geometry"]).area / building["geometry"].area
            if overlap > 0.8:
                if any(k.startswith("roof:") for k in part.get("tags", {})):
                    keep = False
                    break
        if keep:
            filtered.append(building)
    filtered.extend(parts)
    return filtered


def process_tile(client: OverpassClient, bbox: tuple[float, float, float, float]) -> Dict:
    payload = client.query_buildings(bbox)
    return payload


def main() -> None:
    parser = argparse.ArgumentParser(description="OSM roof lead extraction")
    parser.add_argument("--aoi", type=str, default=None)
    parser.add_argument("--bbox", type=str, default=None)
    parser.add_argument("--min_area_m2", type=float, default=300)
    parser.add_argument("--target", type=str, choices=["commercial", "industrial", "mixed"], default="mixed")
    parser.add_argument("--max_candidates", type=int, default=3000)
    parser.add_argument("--tile_size_deg", type=float, default=0.01)
    parser.add_argument("--out_dir", type=str, default="outputs")
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    setup_logging()
    logging.info("Starting pipeline")
    config = PipelineConfig(
        min_area_m2=args.min_area_m2,
        target=args.target,
        max_candidates=args.max_candidates,
        tile_size_deg=args.tile_size_deg,
        out_dir=args.out_dir,
        seed=args.seed,
        strict=args.strict,
    )

    aoi = load_aoi(args.aoi, args.bbox)
    tiles = list(tile_bboxes(args.aoi, args.bbox, args.tile_size_deg))
    logging.info("Generated %s tiles", len(tiles))

    filter_config = FilterConfig(min_area_m2=config.min_area_m2)
    if config.strict:
        filter_config = FilterConfig.strict(filter_config)

    client = OverpassClient(OverpassConfig())
    elements: List[Dict] = []
    stats: Dict[str, int | float] = {
        "tiles": len(tiles),
        "elements": 0,
        "excluded_solar": 0,
        "excluded_building": 0,
        "excluded_target": 0,
        "invalid_geom": 0,
        "filtered_geom": 0,
        "candidates": 0,
        "dedup_removed": 0,
        "min_area_m2": config.min_area_m2,
        "target": config.target,
        "strict": config.strict,
    }

    start_fetch = time.time()
    with ThreadPoolExecutor(max_workers=6) as executor:
        futures = {executor.submit(process_tile, client, tile.bbox): tile for tile in tiles}
        for future in as_completed(futures):
            tile = futures[future]
            try:
                payload = future.result()
            except Exception as exc:
                logging.warning("Tile %s failed: %s", tile.bbox, exc)
                continue
            elements.extend(payload.get("elements", []))
    stats["elements"] = len(elements)
    stats["fetch_seconds"] = round(time.time() - start_fetch, 2)

    parsed = parse_elements(elements)
    logging.info("Parsed %s geometries", len(parsed))

    candidates: List[Dict] = []
    for item in parsed:
        tags = item["tags"]
        if is_excluded_building(tags):
            stats["excluded_building"] += 1
            continue
        if not target_allowed(tags, config.target):
            stats["excluded_target"] += 1
            continue
        solar_state = solar_status(tags)
        if solar_state.startswith("explicit_yes"):
            stats["excluded_solar"] += 1
            continue
        geom = normalize_geometry(item["geometry"])
        if geom is None:
            stats["invalid_geom"] += 1
            continue
        projected, _ = project_to_utm(geom)
        metrics = compute_metrics(projected)
        filter_reasons = geometry_filter(metrics.__dict__, filter_config)
        if filter_reasons:
            stats["filtered_geom"] += 1
            logging.info("Discarded %s due to %s", item["id_osm"], ",".join(filter_reasons))
            continue
        orientation = compute_orientation(tags, projected)
        centroid = geom.centroid
        record = {
            "id_osm": item["id_osm"],
            "type": item["osm_type"],
            "building": building_type(tags),
            "geometry": geom,
            "area_m2": metrics.area_m2,
            "perimeter_m": metrics.perimeter_m,
            "compactness": metrics.compactness,
            "convexity": metrics.convexity,
            "rectangularity": metrics.rectangularity,
            "aspect_ratio": metrics.aspect_ratio,
            "vertex_count": metrics.vertex_count,
            "hole_area_ratio": metrics.hole_area_ratio,
            "min_width_m": metrics.min_width_m,
            "orientation_deg": orientation.orientation_deg,
            "orientation_confidence": orientation.confidence,
            "solar_status": solar_state,
            "centroid_lat": centroid.y,
            "centroid_lon": centroid.x,
            "tags": tags,
        }
        record["pre_score"] = pre_score(metrics.__dict__)
        record["score"] = final_score(metrics.__dict__, orientation.orientation_deg, orientation.confidence, tags, config.target)
        candidates.append(record)

    candidates = prefer_parts(candidates)
    candidates, dedup_removed = deduplicate(candidates)
    stats["dedup_removed"] = dedup_removed

    candidates.sort(key=lambda x: x["score"], reverse=True)
    candidates = candidates[: config.max_candidates]
    stats["candidates"] = len(candidates)

    out_dir = ensure_output_dir(config.out_dir)
    export_geojson(candidates, out_dir / "candidates.geojson")
    export_csv(candidates, out_dir / "candidates.csv")
    export_report(stats, candidates, out_dir / "report.md")
    logging.info("Exported %s candidates to %s", len(candidates), out_dir)


if __name__ == "__main__":
    main()
