#!/usr/bin/env python3
"""Checker for boundary-delta1 uniformity telemetry."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_boundary_delta1_uniformity_scan.py"
CONTRACT = "check_ns_boundary_delta1_uniformity_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_BOUNDARY_DELTA1_UNIFORMITY_SCAN_CHECK"
DEFAULT_SCAN_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_boundary_delta1_uniformity_scan_N128_20260621.json"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "check_ns_boundary_delta1_uniformity_scan_N128_20260621.json"
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scan-json", type=Path, default=DEFAULT_SCAN_JSON)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _fraction_ok(value: Any) -> bool:
    try:
        parsed = float(value)
    except Exception:
        return False
    return math.isfinite(parsed) and 0.0 <= parsed <= 1.0 + 1.0e-9


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def main() -> int:
    args = _parse_args()
    out = Path(args.output_json)
    out.parent.mkdir(parents=True, exist_ok=True)
    errors: list[str] = []
    warnings: list[str] = []
    try:
        payload = _load_json(Path(args.scan_json))
    except Exception as exc:
        result = {"contract": CONTRACT, "route_decision": ROUTE_DECISION, "status": "error", "errors": [str(exc)]}
        out.write_text(_json_text(result, args.pretty), encoding="utf-8")
        return 1

    if payload.get("contract") != "ns_boundary_delta1_uniformity_scan":
        errors.append("unexpected contract")
    frame_rows = payload.get("frame_rows")
    aggregate = payload.get("aggregate")
    if not isinstance(frame_rows, list):
        errors.append("frame_rows missing or not a list")
        frame_rows = []
    if not isinstance(aggregate, dict):
        errors.append("aggregate missing or not a dict")
        aggregate = {}

    ok_rows = [row for row in frame_rows if isinstance(row, dict) and row.get("status") == "ok"]
    for row in ok_rows:
        for band_row in row.get("boundary_band_rows", []):
            if not _fraction_ok(band_row.get("boundary_fraction", -1.0)):
                errors.append(f"bad boundary_fraction on frame {row.get('frame')}")
            if float(band_row.get("operator_delta1_residual_max", -1.0)) < 0.0:
                errors.append(f"negative operator residual on frame {row.get('frame')}")
            if float(band_row.get("frob_delta1_residual_max", -1.0)) < 0.0:
                errors.append(f"negative Frobenius residual on frame {row.get('frame')}")
            for threshold_row in band_row.get("gap_threshold_rows", []):
                if not _fraction_ok(threshold_row.get("active_fraction_of_boundary", -1.0)):
                    errors.append(f"bad active_fraction_of_boundary on frame {row.get('frame')}")
                if not _fraction_ok(threshold_row.get("boundary_gap_separation", -1.0)):
                    errors.append(f"bad boundary_gap_separation on frame {row.get('frame')}")
                quantiles = threshold_row.get("delta1_quantiles", {})
                if not isinstance(quantiles, dict):
                    errors.append(f"quantiles missing on frame {row.get('frame')}")
                else:
                    values = [float(quantiles[key]) for key in ("p05", "p25", "p50", "p75", "p95")]
                    if values != sorted(values):
                        errors.append(f"non-monotone quantiles on frame {row.get('frame')}")

    if aggregate:
        if int(aggregate.get("ok_frames", 0)) != len(ok_rows):
            errors.append("aggregate ok_frames mismatch")
        if int(aggregate.get("boundary_count", 0)) < 0:
            warnings.append("aggregate boundary_count missing")
        for band_row in aggregate.get("band_rows", []):
            if not _fraction_ok(band_row.get("boundary_fraction", -1.0)):
                errors.append("aggregate boundary_fraction invalid")
            for threshold_row in band_row.get("gap_threshold_rows", []):
                if not _fraction_ok(threshold_row.get("active_fraction_of_boundary", -1.0)):
                    errors.append("aggregate active_fraction_of_boundary invalid")
                if not _fraction_ok(threshold_row.get("boundary_gap_separation", -1.0)):
                    errors.append("aggregate boundary_gap_separation invalid")

    result = {
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "script": SCRIPT_NAME,
        "status": "ok" if not errors else "error",
        "errors": errors,
        "warnings": warnings,
        "checked_scan_json": str(args.scan_json),
        "summary": {
            "frame_count": len(frame_rows),
            "ok_frames": len(ok_rows),
            "aggregate_band_count": len(aggregate.get("band_rows", [])) if isinstance(aggregate, dict) else 0,
            "aggregate_gap_threshold_count": len(aggregate.get("gap_threshold_rows", [])) if isinstance(aggregate, dict) else 0,
        },
    }
    out.write_text(_json_text(result, args.pretty), encoding="utf-8")
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
