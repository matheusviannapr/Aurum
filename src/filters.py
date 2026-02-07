"""Filtering logic to remove low-quality roofs."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, List, Tuple

from shapely.geometry import Polygon


SOLAR_TAG_KEYS = {
    "generator:source",
    "generator:method",
    "power",
    "solar_panel",
    "solar_panels",
    "rooftop:solar",
    "roof:solar",
}

EXCLUDED_BUILDING_TYPES = {
    "hut",
    "shed",
    "garage",
    "kiosk",
    "terrace",
    "cabin",
    "roof",
}

PRIORITY_BUILDING_TYPES = {
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


@dataclass
class FilterConfig:
    min_area_m2: float = 300.0
    compactness_min: float = 0.15
    convexity_min: float = 0.75
    rectangularity_min: float = 0.60
    aspect_ratio_max: float = 8.0
    vertex_count_max: int = 80
    hole_area_ratio_max: float = 0.15
    min_width_m: float = 4.0

    @classmethod
    def strict(cls, base: "FilterConfig") -> "FilterConfig":
        return cls(
            min_area_m2=base.min_area_m2,
            compactness_min=0.20,
            convexity_min=0.82,
            rectangularity_min=0.70,
            aspect_ratio_max=6.0,
            vertex_count_max=60,
            hole_area_ratio_max=0.08,
            min_width_m=base.min_width_m,
        )


def has_explicit_solar(tags: Dict[str, str]) -> bool:
    generator_source = tags.get("generator:source") == "solar"
    generator_method = tags.get("generator:method") == "photovoltaic"
    power_solar = tags.get("power") == "generator" and tags.get("generator:source") == "solar"
    solar_yes = tags.get("solar_panel") == "yes" or tags.get("solar_panels") == "yes"
    rooftop = "rooftop:solar" in tags or "roof:solar" in tags
    return generator_source or generator_method or power_solar or solar_yes or rooftop


def solar_status(tags: Dict[str, str]) -> str:
    if has_explicit_solar(tags):
        return "explicit_yes/excluded"
    return "unknown"


def building_type(tags: Dict[str, str]) -> str:
    return tags.get("building") or tags.get("building:part") or "unknown"


def is_excluded_building(tags: Dict[str, str]) -> bool:
    return building_type(tags) in EXCLUDED_BUILDING_TYPES


def is_priority_building(tags: Dict[str, str]) -> bool:
    return building_type(tags) in PRIORITY_BUILDING_TYPES


def geometry_filter(record: Dict[str, float], config: FilterConfig) -> List[str]:
    reasons = []
    if record["area_m2"] < config.min_area_m2:
        reasons.append("area")
    if record["compactness"] < config.compactness_min:
        reasons.append("compactness")
    if record["convexity"] < config.convexity_min:
        reasons.append("convexity")
    if record["rectangularity"] < config.rectangularity_min:
        reasons.append("rectangularity")
    if record["aspect_ratio"] > config.aspect_ratio_max:
        reasons.append("aspect_ratio")
    if record["vertex_count"] > config.vertex_count_max:
        reasons.append("vertex_count")
    if record["hole_area_ratio"] > config.hole_area_ratio_max:
        reasons.append("holes")
    if record["min_width_m"] < config.min_width_m:
        reasons.append("min_width")
    return reasons


def iou(poly_a: Polygon, poly_b: Polygon) -> float:
    intersection = poly_a.intersection(poly_b).area
    union = poly_a.union(poly_b).area
    if union == 0:
        return 0.0
    return intersection / union


def deduplicate(candidates: List[Dict], iou_threshold: float = 0.9) -> Tuple[List[Dict], int]:
    kept: List[Dict] = []
    removed = 0
    for candidate in candidates:
        duplicate = False
        for existing in kept:
            if iou(candidate["geometry"], existing["geometry"]) > iou_threshold:
                duplicate = True
                if candidate.get("pre_score", 0) > existing.get("pre_score", 0):
                    kept.remove(existing)
                    kept.append(candidate)
                    removed += 1
                else:
                    removed += 1
                break
        if not duplicate:
            kept.append(candidate)
    return kept, removed
