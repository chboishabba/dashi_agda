#!/usr/bin/env python3
"""Validate ns_triad_phase_regime_separation_scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

SCRIPT_NAME = "scripts/check_ns_triad_phase_regime_separation_scan.py"
CONTRACT = "check_ns_triad_phase_regime_separation_scan"
SOURCE_CONTRACT = "ns_triad_phase_regime_separation_scan"
SOURCE_SCRIPT_NAME = "scripts/ns_triad_phase_regime_separation_scan.py"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_PHASE_REGIME_SEPARATION_SCAN"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_PHASE_REGIME_SEPARATION_SCAN_CHECK"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_phase_regime_separation_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_triad_phase_regime_separation_scan_N128_20260621.json"
)

SOURCE_CONTROL_CARD = {
    "O": "Measure phase-regime separation for the active NS triad Wall 1 route.",
    "R": "Compare random-phase baselines against optimized low-frustration references on small shell cutoffs and summarize the separation signal.",
    "C": SOURCE_SCRIPT_NAME,
    "S": "Candidate-only telemetry; the phase-regime proxies are empirical only.",
    "L": "Load raw frames, reuse the selected Fourier-vorticity triad machinery, and compare random-phase versus optimized low-frustration shell carriers.",
    "P": SOURCE_ROUTE_DECISION,
    "G": "No theorem, Clay, or route promotion is inferred from this scan.",
    "F": "This scan estimates separation and epsilon-gap proxies only; it does not prove closure.",
}

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


def _check_row(row: dict[str, Any], path: str, errors: list[str]) -> None:
    if row.get("status") not in ALLOWED_STATUSES:
        errors.append(f"{path}.status: must be ok|partial|error")
    if _nonnegative_int(row.get("frame")) is None:
        errors.append(f"{path}.frame: must be nonnegative int")
    if _nonnegative_int(row.get("shell_n")) is None:
        errors.append(f"{path}.shell_n: must be nonnegative int")
    for key in ("candidate_only", "empirical_non_promoting"):
        if row.get(key) is not True:
            errors.append(f"{path}.{key}: must be true")
    if row.get("route_mode") != "fail-closed":
        errors.append(f"{path}.route_mode: must be 'fail-closed'")
    for key in (
        "selected_mode_count",
        "shell_mode_count",
        "triad_count",
        "top_k",
        "pool_multiplier",
        "random_phase_sample_count",
    ):
        if _nonnegative_int(row.get(key)) is None:
            errors.append(f"{path}.{key}: must be nonnegative int")
    for key in (
        "selected_mode_amplitude_sum",
        "phase_field_fit_rmse",
        "optimized_frustration_floor_proxy",
        "optimized_lambda_max_proxy",
        "random_phase_lambda_gap_proxy_mean",
        "random_phase_lambda_max_proxy_mean",
        "random_phase_lambda_max_proxy_p95",
        "random_phase_frustration_floor_proxy_mean",
        "random_phase_frustration_floor_proxy_p95",
    ):
        value = _finite_float(row.get(key))
        if row.get("status") == OK_STATUS and value is None:
            errors.append(f"{path}.{key}: must be finite for ok rows")
        elif value is not None and value < -1.0e-12:
            errors.append(f"{path}.{key}: must be nonnegative")
    if row.get("status") == OK_STATUS:
        _check_fraction(errors, f"{path}.random_phase_alignment_fraction_mean", row.get("random_phase_alignment_fraction_mean"))
    if row.get("warnings") is not None and not isinstance(row.get("warnings"), list):
        errors.append(f"{path}.warnings: must be list or null")
    if row.get("errors") is not None and not isinstance(row.get("errors"), list):
        errors.append(f"{path}.errors: must be list or null")
    candidates = row.get("reference_candidates")
    if candidates is not None and not isinstance(candidates, list):
        errors.append(f"{path}.reference_candidates: must be list or null")


def _check_aggregate(aggregate: dict[str, Any], row_count: int, errors: list[str]) -> None:
    if _nonnegative_int(aggregate.get("processed_frames")) != row_count:
        errors.append("aggregate.processed_frames: must match row count")
    for key in ("ok_frames", "partial_frames", "error_frames"):
        if _nonnegative_int(aggregate.get(key)) is None:
            errors.append(f"aggregate.{key}: must be nonnegative int")
    shells = aggregate.get("shells")
    if not isinstance(shells, list) or not shells:
        errors.append("aggregate.shells: must be non-empty list")
    for key in (
        "optimized_lambda_gap_proxy_mean",
        "optimized_lambda_max_proxy_mean",
        "random_phase_lambda_max_proxy_mean",
        "optimized_frustration_floor_proxy_mean",
    ):
        value = aggregate.get(key)
        if value is not None and _finite_float(value) is None:
            errors.append(f"aggregate.{key}: must be finite or null")
    shell_aggregates = aggregate.get("shell_aggregates")
    if shell_aggregates is not None and not isinstance(shell_aggregates, list):
        errors.append("aggregate.shell_aggregates: must be list or null")


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
    if payload.get("control_card") != SOURCE_CONTROL_CARD:
        errors.append("control_card: must exactly match the producer control card")

    authority = payload.get("authority")
    if not isinstance(authority, dict):
        errors.append("authority: must be object")
    else:
        for key, expected in EXPECTED_AUTHORITY.items():
            if authority.get(key) is not expected:
                errors.append(f"authority.{key}: must be {expected!r}")

    rows = payload.get("phase_regime_separation_rows")
    if not isinstance(rows, list) or not rows:
        errors.append("phase_regime_separation_rows: must be non-empty list")
        rows = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            errors.append(f"rows[{index}]: must be object")
            continue
        _check_row(row, f"rows[{index}]", errors)

    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
    else:
        _check_aggregate(aggregate, len(rows), errors)

    status = OK_STATUS if not errors else ERROR_STATUS
    receipt = {
        "contract": CONTRACT,
        "schema_version": SCHEMA_VERSION,
        "route_decision": ROUTE_DECISION,
        "script_name": SCRIPT_NAME,
        "control_card": {
            "O": "Validate phase-regime separation telemetry output.",
            "R": "Check control card, authority flags, shell rows, and aggregate separation metrics.",
            "C": SCRIPT_NAME,
            "S": "Fail-closed checker for malformed phase-regime telemetry surfaces.",
            "L": "Load the scan JSON, validate rows and aggregates, then emit a checker receipt.",
            "P": ROUTE_DECISION,
            "G": "Checker remains empirical and non-promoting.",
            "F": "Any malformed field, authority drift, or route-marker mismatch is a hard error.",
        },
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
