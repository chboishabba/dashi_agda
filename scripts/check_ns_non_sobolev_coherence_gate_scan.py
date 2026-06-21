#!/usr/bin/env python3
"""Validate ns_non_sobolev_coherence_gate_scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_non_sobolev_coherence_gate_scan.py"
CONTRACT = "check_ns_non_sobolev_coherence_gate_scan"
SOURCE_CONTRACT = "ns_non_sobolev_coherence_gate_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_NON_SOBOLEV_COHERENCE_GATE_SCAN_CHECK"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_non_sobolev_telemetry_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_non_sobolev_coherence_gate_scan_N128_20260621.json"
)

CONTROL_CARD = {
    "O": "Validate non-Sobolev coherence gate telemetry output.",
    "R": "Check schema, authority flags, aggregate rows, and same-H^s-control telemetry fields.",
    "C": SCRIPT_NAME,
    "S": "Fail-closed checker for malformed non-Sobolev telemetry surfaces.",
    "L": "Load the scan JSON, validate rows and aggregates, then emit a checker receipt.",
    "P": ROUTE_DECISION,
    "G": "Checker remains empirical and non-promoting.",
    "F": "Any malformed field or authority drift is a hard error.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source_json", nargs="?", type=Path)
    parser.add_argument("--source-json", type=Path, dest="source_json_kw")
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _input_path(args: argparse.Namespace) -> Path:
    if args.source_json is not None and args.source_json_kw is not None:
        raise ValueError("provide either positional source_json or --source-json, not both")
    if args.source_json is None and args.source_json_kw is None:
        return DEFAULT_SOURCE_JSON
    return args.source_json if args.source_json is not None else args.source_json_kw


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("payload must be object")
    return payload


def _finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _nonnegative_int(value: Any) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if isinstance(value, float) and math.isfinite(value) and value.is_integer() and value >= 0.0:
        return int(value)
    return None


def main() -> int:
    args = _parse_args()
    path = _input_path(args)
    errors: list[str] = []
    warnings: list[str] = []
    try:
        payload = _load_json(path)
    except Exception as exc:  # noqa: BLE001
        receipt = {
            **CONTROL_CARD,
            "contract": CONTRACT,
            "route_decision": ROUTE_DECISION,
            "status": ERROR_STATUS,
            "ok": False,
            "errors": [str(exc)],
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(receipt, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(receipt, args.pretty))
        return 1

    if payload.get("contract") != SOURCE_CONTRACT:
        errors.append(f"contract: must be {SOURCE_CONTRACT!r}")
    if payload.get("status") not in ALLOWED_STATUSES:
        errors.append("status: must be ok|partial|error")

    authority = payload.get("authority")
    if not isinstance(authority, dict):
        errors.append("authority: must be object")
    else:
        expected = {
            "candidate_only": True,
            "empirical_non_promoting": True,
            "truth_authority": False,
            "theorem_authority": False,
            "clay_authority": False,
            "runtime_authority": False,
            "promoted": False,
        }
        for key, value in expected.items():
            if authority.get(key) is not value:
                errors.append(f"authority.{key}: must be {value!r}")

    rows = payload.get("non_sobolev_rows")
    if not isinstance(rows, list) or not rows:
        errors.append("non_sobolev_rows: must be non-empty list")
        rows = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            errors.append(f"non_sobolev_rows[{index}]: must be object")
            continue
        if row.get("status") not in ALLOWED_STATUSES:
            errors.append(f"non_sobolev_rows[{index}].status: must be ok|partial|error")
        if _nonnegative_int(row.get("frame")) is None:
            errors.append(f"non_sobolev_rows[{index}].frame: must be nonnegative int")
        if _finite_float(row.get("orbit_phase")) is None:
            errors.append(f"non_sobolev_rows[{index}].orbit_phase: must be finite")
        if row.get("same_hs_norm_control") is not True:
            errors.append(f"non_sobolev_rows[{index}].same_hs_norm_control: must be true")
        for key in (
            "hs_norm",
            "observed_orbit_coherence",
            "surrogate_coherence_mean",
            "non_sobolev_margin",
            "non_sobolev_score",
            "non_sobolev_strength_gap",
        ):
            if _finite_float(row.get(key)) is None:
                errors.append(f"non_sobolev_rows[{index}].{key}: must be finite")
        if _nonnegative_int(row.get("triad_count")) is None:
            errors.append(f"non_sobolev_rows[{index}].triad_count: must be nonnegative int")

    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
        aggregate = {}
    if _nonnegative_int(aggregate.get("processed_frames")) is None:
        errors.append("aggregate.processed_frames: must be nonnegative int")
    if _finite_float(aggregate.get("same_hs_norm_control_fraction")) is None:
        errors.append("aggregate.same_hs_norm_control_fraction: must be finite")
    for key in (
        "non_sobolev_margin_mean",
        "non_sobolev_score_mean",
        "non_sobolev_strength_gap_mean",
        "hs_norm_mean",
        "margin_vs_hs_norm_correlation",
        "observed_vs_surrogate_coherence_correlation",
    ):
        value = aggregate.get(key)
        if value is not None:
            parsed = _finite_float(value)
            if parsed is None:
                errors.append(f"aggregate.{key}: must be finite or null")
            elif "correlation" in key and (parsed < -1.0 - 1.0e-12 or parsed > 1.0 + 1.0e-12):
                errors.append(f"aggregate.{key}: correlation must lie in [-1,1]")

    receipt = {
        **CONTROL_CARD,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "status": OK_STATUS if not errors else ERROR_STATUS,
        "ok": not errors,
        "warnings": warnings,
        "errors": errors,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(receipt, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(receipt, args.pretty))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
