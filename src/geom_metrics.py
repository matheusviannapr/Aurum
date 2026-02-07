"""Geometry metrics and validation helpers."""
from __future__ import annotations

from dataclasses import dataclass
from math import pi
from typing import Tuple

from pyproj import CRS, Transformer
from shapely.geometry import Polygon, MultiPolygon
from shapely.ops import transform
from shapely.validation import make_valid


@dataclass
class GeometryMetrics:
    area_m2: float
    perimeter_m: float
    compactness: float
    convexity: float
    rectangularity: float
    aspect_ratio: float
    vertex_count: int
    hole_area_ratio: float
    min_width_m: float


def _utm_crs_for(lon: float, lat: float) -> CRS:
    zone = int((lon + 180) / 6) + 1
    hemisphere = "south" if lat < 0 else "north"
    return CRS.from_dict({"proj": "utm", "zone": zone, "south": hemisphere == "south"})


def project_to_utm(geom: Polygon | MultiPolygon) -> Tuple[Polygon | MultiPolygon, CRS]:
    centroid = geom.centroid
    utm = _utm_crs_for(centroid.x, centroid.y)
    transformer = Transformer.from_crs(CRS.from_epsg(4326), utm, always_xy=True)
    projected = transform(transformer.transform, geom)
    return projected, utm


def normalize_geometry(geom: Polygon | MultiPolygon) -> Polygon | MultiPolygon | None:
    valid = make_valid(geom)
    if valid.is_empty:
        return None
    if valid.geom_type == "GeometryCollection":
        polys = [g for g in valid.geoms if g.geom_type in {"Polygon", "MultiPolygon"}]
        if not polys:
            return None
        valid = max(polys, key=lambda g: g.area)
    return valid


def _min_rot_rect_sides(rect: Polygon) -> Tuple[float, float]:
    coords = list(rect.exterior.coords)
    if len(coords) < 4:
        return 0.0, 0.0
    sides = []
    for idx in range(len(coords) - 1):
        x0, y0 = coords[idx]
        x1, y1 = coords[idx + 1]
        sides.append(((x1 - x0) ** 2 + (y1 - y0) ** 2) ** 0.5)
    if not sides:
        return 0.0, 0.0
    return max(sides), min(sides)


def compute_metrics(geom: Polygon | MultiPolygon) -> GeometryMetrics:
    if geom.geom_type == "MultiPolygon":
        geom = max(geom.geoms, key=lambda g: g.area)
    area = geom.area
    perimeter = geom.length
    compactness = 0.0 if perimeter == 0 else (4 * pi * area) / (perimeter**2)
    hull_area = geom.convex_hull.area
    convexity = 0.0 if hull_area == 0 else area / hull_area
    min_rect = geom.minimum_rotated_rectangle
    rect_area = min_rect.area
    rectangularity = 0.0 if rect_area == 0 else area / rect_area
    side_a, side_b = _min_rot_rect_sides(min_rect)
    if side_b == 0:
        aspect_ratio = 0.0
    else:
        aspect_ratio = max(side_a, side_b) / max(1e-6, min(side_a, side_b))
    vertex_count = len(geom.exterior.coords)
    hole_area = sum(Polygon(interior).area for interior in geom.interiors)
    hole_area_ratio = 0.0 if area == 0 else hole_area / area
    min_width = min(side_a, side_b)
    return GeometryMetrics(
        area_m2=area,
        perimeter_m=perimeter,
        compactness=compactness,
        convexity=convexity,
        rectangularity=rectangularity,
        aspect_ratio=aspect_ratio,
        vertex_count=vertex_count,
        hole_area_ratio=hole_area_ratio,
        min_width_m=min_width,
    )
