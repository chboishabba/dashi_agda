#!/usr/bin/env python3
"""Validate ns_triad_frame_stability_scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

SCRIPT_NAME = "scripts/check_ns_triad_frame_stability_scan.py"
CONTRACT = "check_ns_triad_frame_stability_scan"
SOURCE_CONTRACT = "ns_triad_frame_stability_scan"
SOURCE_SCRIPT_NAME = "scripts/ns_triad_frame_stability_scan.py"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_FRAME_STABILITY_SCAN"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_FRAME_STABILITY_SCAN_CHECK"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_frame_stability_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_triad_frame_stability_scan_N128_20260621.json"
)

EXPECTED_AUTHORITY = {
    "candidate_only": True,
    "empirical_non_promoting": True,
    "truth_authority": False,
    "theorem_authority": False,
    "clay_authority": False,
    "runtime_authority": False,
    "promoted": False,
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


def _check_fraction(errors: list[str], path: str, value: Any) -> None:
    parsed = _finite_float(value)
    if parsed is None or parsed < -1.0e-12 or parsed > 1.0 + 1.0e-12:
        errors.append(f"{path}: must be finite fraction in [0,1]")


def _check_optional_nonnegative_float(errors: list[str], path: str, value: Any) -> None:
    if value is None:
        return
    parsed = _finite_float(value)
    if parsed is None or parsed < -1.0e-12:
        errors.append(f"{path}: must be finite nonnegative or null")


def _check_row(row: dict[str, Any], path: str, errors: list[str]) -> None:
    if row.get("status") not in ALLOWED_STATUSES:
        errors.append(f"{path}.status: must be ok|partial|error")
    if _nonnegative_int(row.get("frame")) is None:
        errors.append(f"{path}.frame: must be nonnegative int")
    for key in ("candidate_only", "empirical_non_promoting"):
        if row.get(key) is not True:
            errors.append(f"{path}.{key}: must be true")
    if row.get("route_mode") != "fail-closed":
        errors.append(f"{path}.route_mode: must be 'fail-closed'")
    for key in ("selected_mode_count", "triad_count", "carrier_stratum_count"):
        if _nonnegative_int(row.get(key)) is None:
            errors.append(f"{path}.{key}: must be nonnegative int")
    for key in (
        "triad_positive_backbone_mass_ratio",
        "triad_negative_frame_mass_ratio",
        "frame_stability_proxy",
        "frame_stability_margin_proxy",
        "stratum_internal_mass_ratio",
        "stratum_cross_mass_ratio",
        "stratum_decomposition_proxy",
        "triad_profile_entropy_normalized",
        "stratum_balance_entropy_normalized",
    ):
        value = _finite_float(row.get(key))
        if value is None or value < -1.0e-12:
            errors.append(f"{path}.{key}: must be finite nonnegative")
    if row.get("cocycle_floor_input_available") not in (True, False):
        errors.append(f"{path}.cocycle_floor_input_available: must be boolean")
    if row.get("cocycle_floor_selected_shell") is not None and _nonnegative_int(row.get("cocycle_floor_selected_shell")) is None:
        errors.append(f"{path}.cocycle_floor_selected_shell: must be nonnegative int or null")
    if row.get("cocycle_floor_selected_reference_id") is not None and not isinstance(row.get("cocycle_floor_selected_reference_id"), str):
        errors.append(f"{path}.cocycle_floor_selected_reference_id: must be string or null")
    if row.get("cocycle_floor_selected_reference_kind") is not None and not isinstance(row.get("cocycle_floor_selected_reference_kind"), str):
        errors.append(f"{path}.cocycle_floor_selected_reference_kind: must be string or null")
    _check_optional_nonnegative_float(errors, f"{path}.cocycle_floor_selected_floor_proxy", row.get("cocycle_floor_selected_floor_proxy"))
    _check_optional_nonnegative_float(errors, f"{path}.cocycle_floor_selected_floor_ratio_vs_raw", row.get("cocycle_floor_selected_floor_ratio_vs_raw"))
    if row.get("cocycle_floor_selected_lambda_max_proxy") is not None and _finite_float(row.get("cocycle_floor_selected_lambda_max_proxy")) is None:
        errors.append(f"{path}.cocycle_floor_selected_lambda_max_proxy: must be finite or null")
    _check_optional_nonnegative_float(errors, f"{path}.cocycle_floor_selected_mean_cycle_lower_bound", row.get("cocycle_floor_selected_mean_cycle_lower_bound"))
    _check_optional_nonnegative_float(errors, f"{path}.cocycle_floor_selected_mean_cycle_lower_bound_normalized", row.get("cocycle_floor_selected_mean_cycle_lower_bound_normalized"))
    if row.get("stratum_records") is not None and not isinstance(row.get("stratum_records"), list):
        errors.append(f"{path}.stratum_records: must be list or null")
    if row.get("triad_samples") is not None and not isinstance(row.get("triad_samples"), list):
        errors.append(f"{path}.triad_samples: must be list or null")


def main() -> int:
    args = _parse_args()
    source_json = _input_path(args)
    payload = _load_json(source_json)
    errors: list[str] = []

    if payload.get("contract") != SOURCE_CONTRACT:
        errors.append(f"contract: must be {SOURCE_CONTRACT!r}")
    if payload.get("route_decision") != SOURCE_ROUTE_DECISION:
        errors.append(f"route_decision: must be {SOURCE_ROUTE_DECISION!r}")
    if payload.get("script") != SOURCE_SCRIPT_NAME:
        errors.append(f"script: must be {SOURCE_SCRIPT_NAME!r}")
    authority = payload.get("authority")
    if not isinstance(authority, dict):
        errors.append("authority: must be object")
    else:
        for key, expected in EXPECTED_AUTHORITY.items():
            if authority.get(key) is not expected:
                errors.append(f"authority.{key}: must be {expected!r}")

    rows = payload.get("triad_frame_stability_rows")
    if not isinstance(rows, list) or not rows:
        errors.append("triad_frame_stability_rows: must be non-empty list")
        rows = []
    for index, row in enumerate(rows):
        if isinstance(row, dict):
            _check_row(row, f"triad_frame_stability_rows[{index}]", errors)
        else:
            errors.append(f"triad_frame_stability_rows[{index}]: must be object")

    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
    else:
        if _nonnegative_int(aggregate.get("processed_frames")) != len(rows):
            errors.append("aggregate.processed_frames: must match row count")
        for key in (
            "frame_stability_proxy_mean",
            "frame_stability_margin_proxy_mean",
            "stratum_decomposition_proxy_mean",
            "cocycle_floor_selected_floor_proxy_mean",
            "cocycle_floor_selected_floor_ratio_vs_raw_mean",
            "cocycle_floor_selected_lambda_max_proxy_mean",
            "cocycle_floor_selected_mean_cycle_lower_bound_mean",
            "cocycle_floor_selected_mean_cycle_lower_bound_normalized_mean",
        ):
            value = aggregate.get(key)
            if value is not None and (_finite_float(value) is None or float(value) < -1.0e-12):
                errors.append(f"aggregate.{key}: must be finite nonnegative or null")
        for key in (
            "frame_stability_vs_cocycle_floor_correlation",
            "frame_margin_vs_cocycle_floor_correlation",
            "frame_margin_vs_cocycle_floor_normalized_lower_bound_correlation",
        ):
            value = aggregate.get(key)
            if value is not None and _finite_float(value) is None:
                errors.append(f"aggregate.{key}: must be finite or null")

    status = OK_STATUS if not errors else ERROR_STATUS
    receipt = {
        "contract": CONTRACT,
        "schema_version": SCHEMA_VERSION,
        "route_decision": ROUTE_DECISION,
        "script_name": SCRIPT_NAME,
        "source_json": str(source_json),
        "status": status,
        "ok": status == OK_STATUS,
        "error_count": int(len(errors)),
        "errors": errors,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(receipt, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(receipt, args.pretty))
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
