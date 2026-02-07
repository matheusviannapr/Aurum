"""Parse Overpass JSON into shapely geometries."""
from __future__ import annotations

from typing import Any, Dict, Iterable, List

from shapely.geometry import Polygon, MultiPolygon


def _geom_from_nodes(nodes: List[Dict[str, float]]) -> Polygon | None:
    coords = [(n["lon"], n["lat"]) for n in nodes]
    if len(coords) < 4:
        return None
    if coords[0] != coords[-1]:
        coords.append(coords[0])
    return Polygon(coords)


def _relation_geom(members: List[Dict[str, Any]]) -> MultiPolygon | Polygon | None:
    outers: List[Polygon] = []
    inners: List[Polygon] = []
    for member in members:
        if member.get("type") != "way":
            continue
        geom = _geom_from_nodes(member.get("geometry", []))
        if not geom:
            continue
        if member.get("role") == "inner":
            inners.append(geom)
        else:
            outers.append(geom)
    if not outers:
        return None
    if not inners:
        if len(outers) == 1:
            return outers[0]
        return MultiPolygon(outers)
    merged = []
    for outer in outers:
        holes = [inner.exterior.coords for inner in inners if inner.within(outer)]
        merged.append(Polygon(outer.exterior.coords, holes))
    return MultiPolygon(merged) if len(merged) > 1 else merged[0]


def parse_elements(elements: Iterable[Dict[str, Any]]) -> List[Dict[str, Any]]:
    parsed: List[Dict[str, Any]] = []
    for element in elements:
        geom = None
        if element.get("type") == "way":
            geom = _geom_from_nodes(element.get("geometry", []))
        elif element.get("type") == "relation":
            geom = _relation_geom(element.get("members", []))
        if geom is None:
            continue
        tags = element.get("tags", {})
        parsed.append(
            {
                "id_osm": element.get("id"),
                "osm_type": element.get("type"),
                "tags": tags,
                "geometry": geom,
            }
        )
    return parsed
