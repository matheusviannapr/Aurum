"""Overpass API client with caching and retry."""
from __future__ import annotations

import hashlib
import json
import logging
import os
import threading
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict

import requests

LOGGER = logging.getLogger(__name__)


@dataclass
class OverpassConfig:
    endpoint: str = "https://overpass-api.de/api/interpreter"
    timeout_s: int = 25
    rate_limit_s: float = 1.0
    max_retries: int = 4
    cache_dir: str = ".cache/overpass"


class OverpassClient:
    def __init__(self, config: OverpassConfig | None = None) -> None:
        self.config = config or OverpassConfig()
        self._lock = threading.Lock()
        self._last_request = 0.0
        Path(self.config.cache_dir).mkdir(parents=True, exist_ok=True)

    def _rate_limit(self) -> None:
        with self._lock:
            elapsed = time.time() - self._last_request
            wait_for = self.config.rate_limit_s - elapsed
            if wait_for > 0:
                time.sleep(wait_for)
            self._last_request = time.time()

    def _cache_path(self, query: str) -> str:
        digest = hashlib.sha1(query.encode("utf-8")).hexdigest()
        return os.path.join(self.config.cache_dir, f"{digest}.json")

    def _load_cache(self, query: str) -> Dict[str, Any] | None:
        path = self._cache_path(query)
        if os.path.exists(path):
            with open(path, "r", encoding="utf-8") as handle:
                return json.load(handle)
        return None

    def _save_cache(self, query: str, payload: Dict[str, Any]) -> None:
        path = self._cache_path(query)
        with open(path, "w", encoding="utf-8") as handle:
            json.dump(payload, handle)

    def _request(self, query: str) -> Dict[str, Any]:
        cached = self._load_cache(query)
        if cached is not None:
            return cached

        for attempt in range(self.config.max_retries + 1):
            self._rate_limit()
            try:
                response = requests.post(
                    self.config.endpoint,
                    data={"data": query},
                    timeout=self.config.timeout_s,
                )
            except requests.RequestException as exc:
                backoff = 2**attempt
                LOGGER.warning("Overpass request error: %s (backoff %ss)", exc, backoff)
                time.sleep(backoff)
                continue

            if response.status_code in {429, 504}:
                backoff = 2**attempt
                LOGGER.warning("Overpass status %s (backoff %ss)", response.status_code, backoff)
                time.sleep(backoff)
                continue

            response.raise_for_status()
            payload = response.json()
            self._save_cache(query, payload)
            return payload

        raise RuntimeError("Overpass request failed after retries")

    def query_buildings(self, bbox: tuple[float, float, float, float]) -> Dict[str, Any]:
        south, west, north, east = bbox[1], bbox[0], bbox[3], bbox[2]
        query = (
            f"[out:json][timeout:{self.config.timeout_s}];("
            f"way[\"building\"]({south},{west},{north},{east});"
            f"relation[\"building\"]({south},{west},{north},{east});"
            f"way[\"building:part\"]({south},{west},{north},{east});"
            f"relation[\"building:part\"]({south},{west},{north},{east});"
            f");out tags geom;"
        )
        return self._request(query)
