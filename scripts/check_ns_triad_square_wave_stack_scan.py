#!/usr/bin/env python3
"""Validate square-wave stack spectral-sharpness scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

SCRIPT_NAME = "scripts/check_ns_triad_square_wave_stack_scan.py"
CONTRACT = "check_ns_triad_square_wave_stack_scan"
SOURCE_CONTRACT = "ns_triad_square_wave_stack_scan"
SOURCE_SCRIPT_NAME = "scripts/ns_triad_square_wave_stack_scan.py"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_SPECTRAL_SHARPNESS_SQUARE_WAVE_STACK_SCAN"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_SPECTRAL_SHARPNESS_SQUARE_WAVE_STACK_SCAN_CHECK"
SCHEMA_VERSION = "1.0.0"

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_spectral_sharpness_square_wave_stack_scan_N128_20260623.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_triad_spectral_sharpness_square_wave_stack_scan_N128_20260623.json"
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
        for key in (
            "lambda_min_kn_a",
            "lambda_max_kn_a",
            "n_eff",
            "dissipation_proxy",
            "bkm_proxy",
            "product_separation_lambda_min_times_bkm_proxy",
        ):
            if _finite(row.get(key)) is None:
                errors.append(f"rows[{index}].{key}: must be finite")
        if row.get("branch") not in {"frame-coercive", "low-band", "high-dissipation"}:
            errors.append(f"rows[{index}].branch: invalid")
        if not isinstance(row.get("triple_danger"), bool):
            errors.append(f"rows[{index}].triple_danger: must be bool")
    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
    else:
        if aggregate.get("spectral_sharpness_square_wave_stack_status") != "fail-closed":
            errors.append("aggregate.spectral_sharpness_square_wave_stack_status: must be 'fail-closed'")
        if aggregate.get("no_triple_danger") is not True:
            errors.append("aggregate.no_triple_danger: must be true")
        if aggregate.get("triple_danger_count") != 0:
            errors.append("aggregate.triple_danger_count: must be 0")
        for key in (
            "lambda_min_kn_a_mean",
            "lambda_min_kn_a_min",
            "n_eff_mean",
            "dissipation_proxy_mean",
            "bkm_proxy_mean",
        ):
            if _finite(aggregate.get(key)) is None:
                errors.append(f"aggregate.{key}: must be finite")
    out = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "source_contract": SOURCE_CONTRACT,
        "source_script_name": SOURCE_SCRIPT_NAME,
        "ok": not errors,
        "status": "ok" if not errors else "error",
        "errors": errors,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(out, pretty=args.pretty), encoding="utf-8")
    print(_json_text(out, pretty=args.pretty))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
