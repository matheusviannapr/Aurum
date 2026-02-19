import argparse
import json
import math
import time
from typing import List, Tuple, Dict, Any

import requests
from shapely.geometry import Polygon, MultiPolygon, shape
from shapely.ops import transform
from shapely.validation import make_valid
from pyproj import Transformer, CRS


def _retry_request(method: str, url: str, params: Dict[str, Any] = None, data: Any = None, headers: Dict[str, str] = None, retries: int = 3, backoff: float = 1.5) -> requests.Response:
    attempt = 0
    last_exc = None
    while attempt < retries:
        try:
            resp = requests.request(method, url, params=params, data=data, headers=headers, timeout=60)
            if resp.status_code == 429:
                time.sleep(backoff * (attempt + 1))
                attempt += 1
                continue
            resp.raise_for_status()
            return resp
        except Exception as exc:
            last_exc = exc
            time.sleep(backoff * (attempt + 1))
            attempt += 1
    if last_exc:
        raise last_exc
    raise RuntimeError("Falha de requisição")


def _get_bbox_from_place(place: str) -> Tuple[float, float, float, float]:
    params = {"format": "json", "q": place, "limit": 1}
    headers = {"User-Agent": "aurumlead/1.0"}
    resp = _retry_request("GET", "https://nominatim.openstreetmap.org/search", params=params, headers=headers)
    items = resp.json()
    if not items:
        raise ValueError("Região não encontrada")
    bbox = items[0]["boundingbox"]
    south = float(bbox[0])
    north = float(bbox[1])
    west = float(bbox[2])
    east = float(bbox[3])
    return south, west, north, east


def _fetch_buildings_bbox(bbox: Tuple[float, float, float, float]) -> List[Dict[str, Any]]:
    south, west, north, east = bbox
    q = f"[out:json][timeout:180];(way[\"building\"]({south},{west},{north},{east});relation[\"building\"]({south},{west},{north},{east}););out geom;"
    headers = {"User-Agent": "aurumlead/1.0", "Content-Type": "application/x-www-form-urlencoded"}
    resp = _retry_request("POST", "https://overpass-api.de/api/interpreter", data=q, headers=headers, retries=5)
    data = resp.json()
    return data.get("elements", [])


def _element_polygon(element: Dict[str, Any]) -> Polygon:
    if element.get("type") == "way" and element.get("geometry"):
        coords = [(p["lon"], p["lat"]) for p in element["geometry"]]
        if len(coords) >= 3:
            try:
                poly = Polygon(coords)
            except Exception:
                return None
            if not poly.is_valid:
                poly = make_valid(poly)
            if isinstance(poly, Polygon):
                return poly
            if isinstance(poly, MultiPolygon):
                areas = [(p.area, p) for p in poly.geoms]
                areas.sort(key=lambda x: x[0], reverse=True)
                return areas[0][1] if areas else None
    if element.get("type") == "relation" and element.get("members"):
        try:
            if element.get("geometry"):
                coords = [(p["lon"], p["lat"]) for p in element["geometry"]]
                if len(coords) >= 3:
                    poly = Polygon(coords)
                    if not poly.is_valid:
                        poly = make_valid(poly)
                    if isinstance(poly, Polygon):
                        return poly
        except Exception:
            return None
    return None


def _utm_crs_for_latlon(lat: float, lon: float) -> CRS:
    zone = int((lon + 180) / 6) + 1
    if lat >= 0:
        epsg = 32600 + zone
    else:
        epsg = 32700 + zone
    return CRS.from_epsg(epsg)


def _polygon_area_m2(poly: Polygon) -> float:
    c = poly.centroid
    crs_src = CRS.from_epsg(4326)
    crs_dst = _utm_crs_for_latlon(c.y, c.x)
    transformer = Transformer.from_crs(crs_src, crs_dst, always_xy=True)
    proj = lambda x, y: transformer.transform(x, y)
    poly_p = transform(proj, poly)
    return float(poly_p.area)


def _slugify(text: str) -> str:
    t = text.lower().strip()
    t = t.replace(" ", "-")
    allowed = "abcdefghijklmnopqrstuvwxyz0123456789-"
    return "".join(ch for ch in t if ch in allowed)


def _collect_buildings(place: str = None, bbox: Tuple[float, float, float, float] = None) -> List[Dict[str, Any]]:
    b = bbox if bbox else _get_bbox_from_place(place)
    elements = _fetch_buildings_bbox(b)
    results = []
    for e in elements:
        p = _element_polygon(e)
        if p is None:
            continue
        try:
            area = _polygon_area_m2(p)
        except Exception:
            continue
        tags = e.get("tags", {})
        results.append({
            "id": e.get("id"),
            "type": e.get("type"),
            "area_m2": area,
            "tags": tags,
            "centroid": [p.centroid.y, p.centroid.x]
        })
    results.sort(key=lambda r: r["area_m2"], reverse=True)
    return results


def _parse_bbox(text: str) -> Tuple[float, float, float, float]:
    parts = [p.strip() for p in text.split(",")]
    if len(parts) != 4:
        raise ValueError("BBox inválido")
    south = float(parts[0])
    west = float(parts[1])
    north = float(parts[2])
    east = float(parts[3])
    return south, west, north, east


def main():
    parser = argparse.ArgumentParser(description="Capta maiores telhados de uma região usando OSM")
    parser.add_argument("regiao", nargs="?", default=None, help="Nome da região, cidade ou estado")
    parser.add_argument("--bbox", dest="bbox", default=None, help="BBox sul, oeste, norte, leste")
    parser.add_argument("--top", dest="top", type=int, default=20, help="Quantidade de resultados")
    parser.add_argument("--out", dest="out", default=None, help="Arquivo de saída JSON")
    args = parser.parse_args()

    if not args.regiao and not args.bbox:
        raise SystemExit("Informe regiao ou bbox")

    bbox = _parse_bbox(args.bbox) if args.bbox else None
    results = _collect_buildings(place=args.regiao, bbox=bbox)
    topn = results[: args.top]

    for i, r in enumerate(topn, 1):
        print(f"#{i} id={r['id']} tipo={r['type']} area_m2={r['area_m2']:.2f} centro={r['centroid'][0]:.6f},{r['centroid'][1]:.6f}")

    if args.out:
        payload = {
            "regiao": args.regiao,
            "bbox": bbox,
            "top": args.top,
            "resultados": topn,
        }
        with open(args.out, "w", encoding="utf-8") as f:
            json.dump(payload, f, ensure_ascii=False, indent=2)


if __name__ == "__main__":
    main()

