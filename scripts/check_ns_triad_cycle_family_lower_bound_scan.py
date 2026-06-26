#!/usr/bin/env python3
"""Validate ns_triad_cycle_family_lower_bound_scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

SCRIPT_NAME = "scripts/check_ns_triad_cycle_family_lower_bound_scan.py"
CONTRACT = "check_ns_triad_cycle_family_lower_bound_scan"
SOURCE_CONTRACT = "ns_triad_cycle_family_lower_bound_scan"
SOURCE_SCRIPT_NAME = "scripts/ns_triad_cycle_family_lower_bound_scan.py"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_CYCLE_FAMILY_LOWER_BOUND_SCAN"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_CYCLE_FAMILY_LOWER_BOUND_SCAN_CHECK"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_cycle_family_lower_bound_scan_N128_20260622.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_triad_cycle_family_lower_bound_scan_N128_20260622.json"
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
        "cycle_family_dim",
        "cycle_family_effective_rank",
        "cycle_family_support_coverage",
        "cycle_family_defect_rms",
        "cycle_family_defect_max",
        "cycle_family_lower_bound",
        "cycle_family_lower_bound_normalized_upper",
        "cycle_family_upper_proxy",
        "cycle_family_gram_trace",
        "cycle_family_gram_rank",
        "cycle_family_gram_condition",
        "cycle_family_gram_min_positive_eigenvalue",
        "cycle_family_gram_max_eigenvalue",
        "cycle_family_pinv_trace",
        "cycle_family_regularization",
        "cycle_family_lower_bound_vs_single_mean_ratio",
        "cycle_family_lower_bound_vs_single_max_ratio",
    ):
        value = _finite_float(row.get(key))
        if value is None or value < -1.0e-12:
            errors.append(f"{path}.{key}: must be finite nonnegative")
    norm = _finite_float(row.get("cycle_family_lower_bound_normalized_upper"))
    if norm is not None and norm > 1.0 + 1.0e-12:
        errors.append(f"{path}.cycle_family_lower_bound_normalized_upper: must be within [0,1]")
    gram_min = _finite_float(row.get("cycle_family_gram_min_positive_eigenvalue"))
    gram_max = _finite_float(row.get("cycle_family_gram_max_eigenvalue"))
    gram_cond = _finite_float(row.get("cycle_family_gram_condition"))
    if gram_min is not None and gram_max is not None and gram_max + 1.0e-12 < gram_min:
        errors.append(f"{path}.cycle_family_gram_max_eigenvalue: must dominate min positive eigenvalue")
    if gram_cond is not None and gram_cond > 0.0 and gram_min is not None and gram_max is not None and gram_min > 0.0:
        implied = gram_max / gram_min
        if abs(gram_cond - implied) > max(1.0e-6, 1.0e-6 * implied):
            errors.append(f"{path}.cycle_family_gram_condition: inconsistent with eigenvalue ratio")
    rows_head = row.get("cycle_family_rows_head")
    if rows_head is not None and not isinstance(rows_head, list):
        errors.append(f"{path}.cycle_family_rows_head: must be list or null")


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
        for key in (
            "cycle_family_dim_mean",
            "cycle_family_effective_rank_mean",
            "cycle_family_support_coverage_mean",
            "cycle_family_lower_bound_mean",
            "cycle_family_lower_bound_normalized_upper_mean",
            "cycle_family_gram_condition_mean",
            "cycle_family_gram_rank_mean",
            "cycle_family_regularization_mean",
        ):
            value = aggregate.get(key)
            if value is not None and (_finite_float(value) is None or float(value) < -1.0e-12):
                errors.append(f"aggregate.{key}: must be finite nonnegative or null")

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
