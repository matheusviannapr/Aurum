"""Utilities for loading AOI and generating tiles."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, List, Tuple

import geopandas as gpd
from shapely.geometry import box, Polygon


@dataclass
class Tile:
    bbox: Tuple[float, float, float, float]


def load_aoi(aoi_path: str | None, bbox_str: str | None) -> Polygon:
    if aoi_path:
        gdf = gpd.read_file(aoi_path)
        if gdf.empty:
            raise ValueError("AOI file has no geometries")
        geom = gdf.unary_union
    elif bbox_str:
        parts = [float(x) for x in bbox_str.split(",")]
        if len(parts) != 4:
            raise ValueError("bbox must be minLon,minLat,maxLon,maxLat")
        geom = box(parts[0], parts[1], parts[2], parts[3])
    else:
        raise ValueError("Either --aoi or --bbox must be provided")
    return geom


def adaptive_tile_size_deg(aoi: Polygon, base_size: float) -> float:
    minx, miny, maxx, maxy = aoi.bounds
    max_dim = max(maxx - minx, maxy - miny)
    if max_dim > 1.0:
        return min(base_size, max_dim / 80)
    if max_dim > 0.2:
        return min(base_size, max_dim / 40)
    return base_size


def generate_tiles(aoi: Polygon, tile_size_deg: float) -> List[Tile]:
    minx, miny, maxx, maxy = aoi.bounds
    tiles: List[Tile] = []
    x = minx
    while x < maxx:
        y = miny
        while y < maxy:
            tile_bbox = (x, y, min(x + tile_size_deg, maxx), min(y + tile_size_deg, maxy))
            tile_geom = box(*tile_bbox)
            if tile_geom.intersects(aoi):
                tiles.append(Tile(bbox=tile_bbox))
            y += tile_size_deg
        x += tile_size_deg
    return tiles


def tile_bboxes(aoi_path: str | None, bbox_str: str | None, tile_size_deg: float) -> Iterable[Tile]:
    aoi = load_aoi(aoi_path, bbox_str)
    size = adaptive_tile_size_deg(aoi, tile_size_deg)
    return generate_tiles(aoi, size)
