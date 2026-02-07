"""Orientation inference and scoring helpers."""
from __future__ import annotations

from dataclasses import dataclass
from math import atan2, degrees
from typing import Dict, Tuple

from shapely.geometry import Polygon, MultiPolygon


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
class OrientationResult:
    orientation_deg: float | None
    confidence: str
    source: str


def _angle_from_vector(dx: float, dy: float) -> float:
    angle = degrees(atan2(dx, dy))
    if angle < 0:
        angle += 360
    return angle


def _infer_from_geom(geom: Polygon | MultiPolygon) -> float | None:
    if geom.geom_type == "MultiPolygon":
        geom = max(geom.geoms, key=lambda g: g.area)
    rect = geom.minimum_rotated_rectangle
    coords = list(rect.exterior.coords)
    if len(coords) < 4:
        return None
    sides = []
    for idx in range(len(coords) - 1):
        x0, y0 = coords[idx]
        x1, y1 = coords[idx + 1]
        length = ((x1 - x0) ** 2 + (y1 - y0) ** 2) ** 0.5
        sides.append((length, x1 - x0, y1 - y0))
    sides.sort(reverse=True)
    _, dx, dy = sides[0]
    return _angle_from_vector(dx, dy)


def orientation_from_tags(tags: Dict[str, str]) -> OrientationResult | None:
    if "roof:direction" in tags:
        try:
            return OrientationResult(float(tags["roof:direction"]) % 360, "high", "roof:direction")
        except ValueError:
            return None
    if "roof:orientation" in tags:
        value = tags["roof:orientation"].upper()
        if value in ORIENTATION_MAP:
            return OrientationResult(float(ORIENTATION_MAP[value]), "high", "roof:orientation")
    return None


def compute_orientation(tags: Dict[str, str], geom: Polygon | MultiPolygon) -> OrientationResult:
    from_tags = orientation_from_tags(tags)
    if from_tags:
        return from_tags
    inferred = _infer_from_geom(geom)
    if inferred is None:
        return OrientationResult(None, "none", "none")
    return OrientationResult(inferred, "low", "inferred")


def orientation_bonus(orientation_deg: float | None, confidence: str) -> float:
    if orientation_deg is None:
        return 0.0
    north = (orientation_deg >= 315 or orientation_deg <= 45)
    south = 135 <= orientation_deg <= 225
    if confidence == "high":
        if north:
            return 8.0
        if south:
            return -4.0
    if confidence == "low":
        if north:
            return 4.0
        if south:
            return -2.0
    return 0.0
