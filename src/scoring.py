"""Scoring for candidate roofs."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Dict

from .orientation import orientation_bonus


@dataclass
class ScoreConfig:
    min_area_m2: float = 300.0
    max_area_m2: float = 2000.0


def area_score(area_m2: float, config: ScoreConfig) -> float:
    if area_m2 <= config.min_area_m2:
        return 0.0
    if area_m2 >= config.max_area_m2:
        return 40.0
    ratio = (area_m2 - config.min_area_m2) / (config.max_area_m2 - config.min_area_m2)
    return 40.0 * ratio


def geometry_score(metrics: Dict[str, float]) -> float:
    score = (
        metrics["rectangularity"] * 18
        + metrics["convexity"] * 15
        + metrics["compactness"] * 12
    )
    aspect_penalty = max(0.0, metrics["aspect_ratio"] - 2.5) * 1.5
    return max(0.0, min(45.0, score - aspect_penalty))


def tag_confidence_score(tags: Dict[str, str]) -> float:
    score = 0.0
    if "building:levels" in tags or "height" in tags:
        score += 2.5
    if "roof:shape" in tags or "roof:material" in tags:
        score += 2.5
    return min(5.0, score)


def final_score(metrics: Dict[str, float], orientation_deg: float | None, orientation_confidence: str, tags: Dict[str, str], target: str) -> float:
    score = area_score(metrics["area_m2"], ScoreConfig())
    score += geometry_score(metrics)
    score += orientation_bonus(orientation_deg, orientation_confidence)
    score += tag_confidence_score(tags)
    if target in {"commercial", "industrial"}:
        if tags.get("building") == "residential" and metrics["area_m2"] < 800:
            score -= 15.0
    return max(0.0, min(100.0, score))


def pre_score(metrics: Dict[str, float]) -> float:
    return area_score(metrics["area_m2"], ScoreConfig()) + geometry_score(metrics)
