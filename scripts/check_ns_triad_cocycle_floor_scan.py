#!/usr/bin/env python3
"""Validate ns_triad_cocycle_floor_scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

SCRIPT_NAME = "scripts/check_ns_triad_cocycle_floor_scan.py"
CONTRACT = "check_ns_triad_cocycle_floor_scan"
SOURCE_CONTRACT = "ns_triad_cocycle_floor_scan"
SOURCE_SCRIPT_NAME = "scripts/ns_triad_cocycle_floor_scan.py"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_COCYCLE_FLOOR_SCAN"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_COCYCLE_FLOOR_SCAN_CHECK"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_cocycle_floor_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_triad_cocycle_floor_scan_N128_20260621.json"
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


def _check_row(row: dict[str, Any], path: str, errors: list[str]) -> None:
    if row.get("status") not in ALLOWED_STATUSES:
        errors.append(f"{path}.status: must be ok|partial|error")
    if _nonnegative_int(row.get("frame")) is None:
        errors.append(f"{path}.frame: must be nonnegative int")
    if _nonnegative_int(row.get("shell")) is None:
        errors.append(f"{path}.shell: must be nonnegative int")
    for key in ("candidate_only", "empirical_non_promoting"):
        if row.get(key) is not True:
            errors.append(f"{path}.{key}: must be true")
    for key in (
        "selected_mode_count",
        "triad_count",
    ):
        if _nonnegative_int(row.get(key)) is None:
            errors.append(f"{path}.{key}: must be nonnegative int")
    for key in (
        "best_reference_floor_proxy",
        "best_reference_floor_rmse",
        "best_reference_lambda_max_proxy",
        "frustration_floor_ratio_vs_raw",
        "cycle_rank_proxy",
        "defective_cycle_count",
        "max_cycle_lower_bound",
        "mean_cycle_lower_bound",
        "cycle_lower_bound_sum",
        "cocycle_defect_mean",
        "cocycle_defect_max",
    ):
        value = _finite_float(row.get(key))
        if value is None or value < -1.0e-12:
            errors.append(f"{path}.{key}: must be finite nonnegative")
    best_floor_proxy = _finite_float(row.get("best_reference_floor_proxy"))
    best_floor_rmse = _finite_float(row.get("best_reference_floor_rmse"))
    best_lambda_max = _finite_float(row.get("best_reference_lambda_max_proxy"))
    floor_ratio = _finite_float(row.get("frustration_floor_ratio_vs_raw"))
    max_cycle_lower_bound = _finite_float(row.get("max_cycle_lower_bound"))
    mean_cycle_lower_bound = _finite_float(row.get("mean_cycle_lower_bound"))
    cycle_lower_bound_sum = _finite_float(row.get("cycle_lower_bound_sum"))
    cocycle_defect_mean = _finite_float(row.get("cocycle_defect_mean"))
    cocycle_defect_max = _finite_float(row.get("cocycle_defect_max"))
    if best_floor_proxy is not None and best_floor_rmse is not None and best_floor_rmse + 1.0e-12 < best_floor_proxy:
        errors.append(f"{path}.best_reference_floor_rmse: must dominate best_reference_floor_proxy")
    if best_lambda_max is not None and not (0.0 - 1.0e-12 <= best_lambda_max <= 1.0 + 1.0e-12):
        errors.append(f"{path}.best_reference_lambda_max_proxy: must be within [0, 1]")
    if floor_ratio is not None and not (0.0 - 1.0e-12 <= floor_ratio <= 1.0 + 1.0e-12):
        errors.append(f"{path}.frustration_floor_ratio_vs_raw: must be within [0, 1]")
    if max_cycle_lower_bound is not None and mean_cycle_lower_bound is not None and max_cycle_lower_bound + 1.0e-12 < mean_cycle_lower_bound:
        errors.append(f"{path}.max_cycle_lower_bound: must dominate mean_cycle_lower_bound")
    if cycle_lower_bound_sum is not None and max_cycle_lower_bound is not None and cycle_lower_bound_sum + 1.0e-12 < max_cycle_lower_bound:
        errors.append(f"{path}.cycle_lower_bound_sum: must dominate max_cycle_lower_bound")
    if cocycle_defect_mean is not None and cocycle_defect_max is not None and cocycle_defect_max + 1.0e-12 < cocycle_defect_mean:
        errors.append(f"{path}.cocycle_defect_max: must dominate cocycle_defect_mean")
    for key, value in row.items():
        if isinstance(key, str) and (key.endswith("_lower_bound") or key.endswith("_floor_ratio")):
            parsed = _finite_float(value)
            if parsed is None or parsed < -1.0e-12:
                errors.append(f"{path}.{key}: must be finite nonnegative")
    if row.get("cycle_records_head") is not None and not isinstance(row.get("cycle_records_head"), list):
        errors.append(f"{path}.cycle_records_head: must be list or null")
    cycle_records = row.get("cycle_records_head")
    if isinstance(cycle_records, list):
        for index, record in enumerate(cycle_records):
            record_path = f"{path}.cycle_records_head[{index}]"
            if not isinstance(record, dict):
                errors.append(f"{record_path}: must be object")
                continue
            for key in ("cycle_index",):
                if _nonnegative_int(record.get(key)) is None:
                    errors.append(f"{record_path}.{key}: must be nonnegative int")
            dual_norm = _finite_float(record.get("cycle_dual_norm"))
            if dual_norm is None or dual_norm < -1.0e-12:
                errors.append(f"{record_path}.cycle_dual_norm: must be finite nonnegative")
            raw_defect = _finite_float(record.get("cycle_raw_defect"))
            if raw_defect is None:
                errors.append(f"{record_path}.cycle_raw_defect: must be finite")
            cycle_defect = _finite_float(record.get("cycle_defect"))
            if cycle_defect is None or cycle_defect < -1.0e-12:
                errors.append(f"{record_path}.cycle_defect: must be finite nonnegative")
            cycle_lower_bound = _finite_float(record.get("cycle_lower_bound"))
            if cycle_lower_bound is None or cycle_lower_bound < -1.0e-12:
                errors.append(f"{record_path}.cycle_lower_bound: must be finite nonnegative")
            if cycle_defect is not None and cycle_defect > math.pi + 1.0e-12:
                errors.append(f"{record_path}.cycle_defect: must be at most pi")


def main() -> int:
    args = _parse_args()
    source_json = _input_path(args)
    payload = _load_json(source_json)
    errors: list[str] = []

    if payload.get("contract") != SOURCE_CONTRACT:
        errors.append(f"contract: must be {SOURCE_CONTRACT!r}")
    if payload.get("route_decision") != SOURCE_ROUTE_DECISION:
        errors.append(f"route_decision: must be {SOURCE_ROUTE_DECISION!r}")
    if payload.get("script_name") != SOURCE_SCRIPT_NAME:
        errors.append(f"script_name: must be {SOURCE_SCRIPT_NAME!r}")
    authority = payload.get("authority")
    if not isinstance(authority, dict):
        errors.append("authority: must be object")
    else:
        for key, expected in EXPECTED_AUTHORITY.items():
            if authority.get(key) is not expected:
                errors.append(f"authority.{key}: must be {expected!r}")

    rows = payload.get("rows")
    if not isinstance(rows, list) or not rows:
        errors.append("rows: must be non-empty list")
        rows = []
    for index, row in enumerate(rows):
        if isinstance(row, dict):
            _check_row(row, f"rows[{index}]", errors)
        else:
            errors.append(f"rows[{index}]: must be object")

    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
    else:
        if _nonnegative_int(aggregate.get("processed_rows")) != len(rows):
            errors.append("aggregate.processed_rows: must match row count")
        if aggregate.get("wall1_status") not in (None, "unproved"):
            errors.append("aggregate.wall1_status: if present must be 'unproved'")
        for key in (
            "cycle_rank_proxy_mean",
            "mean_cycle_lower_bound_mean",
            "max_cycle_lower_bound_mean",
            "frustration_floor_ratio_vs_raw_mean",
            "best_reference_lambda_max_proxy_mean",
            "cocycle_defect_mean_mean",
        ):
            value = aggregate.get(key)
            if value is not None and _finite_float(value) is None:
                errors.append(f"aggregate.{key}: must be finite or null")
        for key in (
            "cycle_rank_proxy_mean",
            "mean_cycle_lower_bound_mean",
            "max_cycle_lower_bound_mean",
            "frustration_floor_ratio_vs_raw_mean",
            "best_reference_lambda_max_proxy_mean",
            "cocycle_defect_mean_mean",
        ):
            value = _finite_float(aggregate.get(key))
            if value is not None and value < -1.0e-12:
                errors.append(f"aggregate.{key}: must be nonnegative when present")
        for key in ("frustration_floor_ratio_vs_raw_mean", "best_reference_lambda_max_proxy_mean"):
            value = _finite_float(aggregate.get(key))
            if value is not None and value > 1.0 + 1.0e-12:
                errors.append(f"aggregate.{key}: must be within [0, 1]")
        mean_lower = _finite_float(aggregate.get("mean_cycle_lower_bound_mean"))
        max_lower = _finite_float(aggregate.get("max_cycle_lower_bound_mean"))
        if mean_lower is not None and max_lower is not None and max_lower + 1.0e-12 < mean_lower:
            errors.append("aggregate.max_cycle_lower_bound_mean: must dominate mean_cycle_lower_bound_mean")

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
