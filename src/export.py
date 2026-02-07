"""Export candidates and report."""
from __future__ import annotations

import json
from pathlib import Path
from typing import Dict, List

import geopandas as gpd
import pandas as pd


def export_geojson(candidates: List[Dict], out_path: Path) -> None:
    gdf = gpd.GeoDataFrame(candidates, geometry="geometry", crs="EPSG:4326")
    gdf.to_file(out_path, driver="GeoJSON")


def export_csv(candidates: List[Dict], out_path: Path) -> None:
    df = pd.DataFrame(candidates)
    if "geometry" in df.columns:
        df = df.drop(columns=["geometry"])
    df.to_csv(out_path, index=False)


def export_report(stats: Dict[str, int | float], candidates: List[Dict], out_path: Path) -> None:
    top = sorted(candidates, key=lambda x: x["score"], reverse=True)[:50]
    lines = ["# Roof Lead Report", "", "## Summary"]
    for key, value in stats.items():
        lines.append(f"- **{key}**: {value}")
    lines.append("")
    lines.append("## Top 50 Candidates")
    for cand in top:
        lines.append(
            f"- {cand['id_osm']} | score {cand['score']:.2f} | area {cand['area_m2']:.1f} m2 | building {cand.get('building')}")
    out_path.write_text("\n".join(lines), encoding="utf-8")


def ensure_output_dir(out_dir: str) -> Path:
    path = Path(out_dir)
    path.mkdir(parents=True, exist_ok=True)
    return path
