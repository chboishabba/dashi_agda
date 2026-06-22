#!/usr/bin/env python3
"""Validate signed mod-2 gaugeability scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

SCRIPT_NAME = "scripts/check_ns_triad_signed_xor_gaugeability_scan.py"
CONTRACT = "check_ns_triad_signed_xor_gaugeability_scan"
SOURCE_CONTRACT = "ns_triad_signed_xor_gaugeability_scan"
SOURCE_SCRIPT_NAME = "scripts/ns_triad_signed_xor_gaugeability_scan.py"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_SIGNED_XOR_GAUGEABILITY_SCAN"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_SIGNED_XOR_GAUGEABILITY_SCAN_CHECK"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_signed_xor_gaugeability_scan_N128_20260622.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_triad_signed_xor_gaugeability_scan_N128_20260622.json"
)


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


def _finite(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _fraction(value: Any) -> float | None:
    parsed = _finite(value)
    if parsed is None or parsed < -1.0e-12 or parsed > 1.0 + 1.0e-12:
        return None
    return parsed


def main() -> int:
    args = _parse_args()
    payload = _load_json(_input_path(args))
    errors: list[str] = []
    if payload.get("contract") != SOURCE_CONTRACT:
        errors.append(f"contract: must be {SOURCE_CONTRACT!r}")
    if payload.get("route_decision") != SOURCE_ROUTE_DECISION:
        errors.append(f"route_decision: must be {SOURCE_ROUTE_DECISION!r}")
    if payload.get("script_name") != SOURCE_SCRIPT_NAME:
        errors.append(f"script_name: must be {SOURCE_SCRIPT_NAME!r}")
    rows = payload.get("rows")
    if not isinstance(rows, list):
        errors.append("rows: must be list")
        rows = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            errors.append(f"rows[{index}]: must be object")
            continue
        if row.get("status") not in {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}:
            errors.append(f"rows[{index}].status: invalid")
        for key in (
            "psi_pi_weight_fraction",
            "psi_zero_weight_fraction",
            "psi_sign_balance_gap_abs",
            "signed_xor_weighted_distance_fraction",
            "signed_xor_distance_vs_balance_capacity",
        ):
            value = row.get(key)
            if value is not None and _fraction(value) is None:
                errors.append(f"rows[{index}].{key}: must be fraction or null")
        for key in ("psi_pi_weight", "psi_zero_weight", "signed_xor_weighted_distance"):
            value = row.get(key)
            if value is not None and (_finite(value) is None or float(value) < -1.0e-12):
                errors.append(f"rows[{index}].{key}: must be finite nonnegative or null")
    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
    else:
        if aggregate.get("wall1a_status") != "unproved":
            errors.append("aggregate.wall1a_status: must be 'unproved'")
        for key in (
            "psi_pi_weight_fraction_mean",
            "signed_xor_weighted_distance_fraction_mean",
            "signed_xor_distance_vs_balance_capacity_mean",
            "signed_xor_gaugeable_fraction",
        ):
            value = aggregate.get(key)
            if value is not None and _fraction(value) is None:
                errors.append(f"aggregate.{key}: must be fraction or null")
    out = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "source_contract": SOURCE_CONTRACT,
        "source_script_name": SOURCE_SCRIPT_NAME,
        "ok": not errors,
        "status": OK_STATUS if not errors else ERROR_STATUS,
        "errors": errors,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(out, pretty=args.pretty), encoding="utf-8")
    print(_json_text(out, pretty=args.pretty))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
