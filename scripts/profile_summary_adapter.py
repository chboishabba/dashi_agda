#!/usr/bin/env python3
"""Precomputed-artifact-first adapter for profile-summary search.

This module intentionally does not reimplement the Hecke logic in Python.
It reads a materialized artifact keyed by current generator name and returns the
full 15-lane `profileSummaryFamily` payload expected by the search script.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_ARTIFACT = ROOT / "artifacts" / "hecke" / "profile_summary_family.json"
REQUIRED_FIELDS = (
    "forcedStableCount",
    "motifChangeCount",
    "totalDrift",
    "repatterningCount",
    "contractiveCount",
    "expansiveCount",
)


def _artifact_path() -> Path:
    override = os.environ.get("DASHI_PROFILE_SUMMARY_ARTIFACT")
    return Path(override) if override else DEFAULT_ARTIFACT


def _load_artifact() -> dict[str, Any]:
    artifact_path = _artifact_path()
    if not artifact_path.exists():
        raise NotImplementedError(
            "No profile-summary artifact found at "
            f"{artifact_path}. Materialize profileSummaryFamily into this JSON "
            "file or override the path with DASHI_PROFILE_SUMMARY_ARTIFACT."
        )
    with artifact_path.open("r", encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise TypeError("profile-summary artifact root must be a JSON object")
    return payload


def _validate_lane(generator_name: str, lane_index: int, lane: Any) -> dict[str, int]:
    if not isinstance(lane, dict):
        raise TypeError(
            f"{generator_name}[{lane_index}] must be a JSON object, got {type(lane)!r}"
        )
    missing = [field for field in REQUIRED_FIELDS if field not in lane]
    if missing:
        raise KeyError(
            f"{generator_name}[{lane_index}] is missing required fields: {', '.join(missing)}"
        )
    return {field: int(lane[field]) for field in REQUIRED_FIELDS}


def profile_summary_family(generator_name: str):
    payload = _load_artifact()
    if generator_name not in payload:
        available = ", ".join(sorted(payload.keys()))
        raise KeyError(
            f"{generator_name!r} is not present in the profile-summary artifact. "
            f"Available keys: {available}"
        )
    lanes = payload[generator_name]
    if not isinstance(lanes, list):
        raise TypeError(f"{generator_name!r} must map to a JSON array of 15 lanes")
    if len(lanes) != 15:
        raise ValueError(
            f"{generator_name!r} must map to exactly 15 lanes, found {len(lanes)}"
        )
    return [_validate_lane(generator_name, lane_index, lane) for lane_index, lane in enumerate(lanes)]
