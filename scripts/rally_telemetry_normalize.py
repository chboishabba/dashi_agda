#!/usr/bin/env python3
"""Normalize provenance-bearing rally telemetry JSONL into the DASHI rally ABI.

This is transport/representation normalization only.  It does not infer road
truth, surface truth, exact event time, or privileged simulator state.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any, Dict, Iterable

CANONICAL_ALIASES = {
    "simulation_time": "simulationTime",
    "time": "simulationTime",
    "frame": "frameIndex",
    "frame_index": "frameIndex",
    "stage_distance": "stageDistance",
    "distance": "stageDistance",
    "position": "position",
    "orientation": "orientation",
    "velocity": "linearVelocity",
    "angular_velocity": "angularVelocity",
    "acceleration": "linearAcceleration",
    "steering": "steeringInput",
    "throttle": "throttleInput",
    "brake": "brakeInput",
    "clutch": "clutchInput",
    "gear": "gear",
    "rpm": "engineSpeed",
    "wheel_speed": "wheelSpeed",
    "suspension_position": "suspensionPosition",
    "suspension_velocity": "suspensionVelocity",
    "tyre_slip": "tyreSlip",
    "tire_slip": "tyreSlip",
    "tyre_load": "tyreLoad",
    "tire_load": "tyreLoad",
    "tyre_temperature": "tyreTemperature",
    "tire_temperature": "tyreTemperature",
    "surface": "surfaceHint",
    "pace_call": "paceCallToken",
    "rendered_frame": "renderedFrame",
}

CANONICAL_SIGNALS = {
    "simulationTime", "frameIndex", "stageDistance", "position", "orientation",
    "linearVelocity", "angularVelocity", "linearAcceleration", "steeringInput",
    "throttleInput", "brakeInput", "clutchInput", "gear", "engineSpeed",
    "wheelSpeed", "suspensionPosition", "suspensionVelocity", "tyreSlip",
    "tyreLoad", "tyreTemperature", "surfaceHint", "paceCallToken",
    "renderedFrame",
}

REQUIRED = {
    "source", "source_field", "value", "source_time", "source_frame",
    "provenance", "provenance_reference",
}


def canonical_signal(row: Dict[str, Any]) -> str:
    explicit = row.get("canonical_signal")
    if explicit is not None:
        if explicit not in CANONICAL_SIGNALS:
            raise ValueError(f"unknown canonical_signal: {explicit}")
        return explicit
    key = str(row["source_field"]).strip().lower()
    try:
        return CANONICAL_ALIASES[key]
    except KeyError as exc:
        raise ValueError(
            f"no canonical mapping for source_field={row['source_field']!r}; "
            "supply canonical_signal explicitly"
        ) from exc


def normalize_row(row: Dict[str, Any], line_number: int) -> Dict[str, Any]:
    missing = REQUIRED.difference(row)
    if missing:
        raise ValueError(f"line {line_number}: missing fields: {sorted(missing)}")

    return {
        "canonical_signal": canonical_signal(row),
        "canonical_value": row["value"],
        "canonical_time_reference": str(row["source_time"]),
        "canonical_station_reference": str(row.get("stage_station", "unresolved")),
        "source_receipt": {
            "source": row["source"],
            "source_field": row["source_field"],
            "source_clock_reference": str(row["source_time"]),
            "source_frame_reference": str(row["source_frame"]),
            "provenance": row["provenance"],
            "provenance_reference": row["provenance_reference"],
            "unit": row.get("unit"),
        },
        "normalisation_reference": row.get(
            "normalisation_reference", "scripts/rally_telemetry_normalize.py"
        ),
    }


def load_jsonl(path: Path) -> Iterable[Dict[str, Any]]:
    with path.open("r", encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, 1):
            stripped = line.strip()
            if not stripped:
                continue
            row = json.loads(stripped)
            if not isinstance(row, dict):
                raise ValueError(f"line {line_number}: JSON value must be an object")
            yield normalize_row(row, line_number)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()

    raw_bytes = args.input.read_bytes()
    rows = list(load_jsonl(args.input))

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, sort_keys=True, separators=(",", ":")))
            handle.write("\n")

    if args.receipt:
        receipt = {
            "input_sha256": hashlib.sha256(raw_bytes).hexdigest(),
            "sample_count": len(rows),
            "canonical_signals": sorted({row["canonical_signal"] for row in rows}),
            "source_provenance_retained": True,
            "clock_lineage_retained": True,
            "privileged_truth_promoted": False,
            "claims_exact_cross_clock_synchronisation": False,
            "claims_physical_truth": False,
        }
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(
            json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
