#!/usr/bin/env python3
"""Validate ns_triad_phase_laplacian_scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_triad_phase_laplacian_scan.py"
CONTRACT = "check_ns_triad_phase_laplacian_scan"
SOURCE_CONTRACT = "ns_triad_phase_laplacian_scan"
SOURCE_SCRIPT_NAME = "scripts/ns_triad_phase_laplacian_scan.py"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_PHASE_LAPLACIAN_SCAN"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_PHASE_LAPLACIAN_SCAN_CHECK"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_phase_laplacian_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_triad_phase_laplacian_scan_N128_20260621.json"
)

SOURCE_CONTROL_CARD = {
    "O": "Measure candidate triad phase-graph Laplacian telemetry on the raw N128 archive.",
    "R": (
        "Build a finite-dimensional phase graph from resonant selected-mode triads, then "
        "summarize unsigned and signed Laplacian proxies together with negative-frame stability metrics."
    ),
    "C": SOURCE_SCRIPT_NAME,
    "S": "Telemetry only; the phase-graph carrier is empirical and non-promoting.",
    "L": (
        "Load raw frames, select dominant modes, form resonant triads, assemble Laplacian proxies, "
        "and emit framewise plus aggregate stability diagnostics."
    ),
    "P": SOURCE_ROUTE_DECISION,
    "G": "No theorem, Clay, or route promotion is inferred from this scan.",
    "F": "The finite carrier may expose stability structure, but it does not prove any operator bound.",
}

CONTROL_CARD = {
    "O": "Validate triad phase-Laplacian telemetry output.",
    "R": "Check control card, authority flags, fail-closed markers, row metrics, and aggregate reconciliation.",
    "C": SCRIPT_NAME,
    "S": "Fail-closed checker for malformed triad phase-Laplacian telemetry surfaces.",
    "L": "Load the scan JSON, validate rows and aggregates, then emit a checker receipt.",
    "P": ROUTE_DECISION,
    "G": "Checker remains empirical and non-promoting.",
    "F": "Any malformed field, authority drift, or route-marker mismatch is a hard error.",
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


def _check_numeric_or_null(value: Any, path: str, errors: list[str], *, nonnegative: bool = False) -> None:
    parsed = _finite_float(value)
    if parsed is None:
        if value is not None:
            errors.append(f"{path}: must be finite or null")
        return
    if nonnegative and parsed < -1.0e-12:
        errors.append(f"{path}: must be nonnegative")


def _check_payload(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []

    if payload.get("contract") != SOURCE_CONTRACT:
        errors.append(f"contract: must be {SOURCE_CONTRACT!r}")
    if payload.get("schema_version") != SCHEMA_VERSION:
        errors.append(f"schema_version: must be {SCHEMA_VERSION!r}")
    if payload.get("route_decision") != SOURCE_ROUTE_DECISION:
        errors.append(f"route_decision: must be {SOURCE_ROUTE_DECISION!r}")
    if payload.get("script") != SOURCE_SCRIPT_NAME:
        errors.append(f"script: must be {SOURCE_SCRIPT_NAME!r}")
    if payload.get("status") not in ALLOWED_STATUSES:
        errors.append(f"status: must be one of {sorted(ALLOWED_STATUSES)!r}")
    if payload.get("route_mode") != "fail-closed":
        errors.append("route_mode: must be 'fail-closed'")
    if payload.get("fail_closed") is not True:
        errors.append("fail_closed: must be true")
    if payload.get("control_card") != SOURCE_CONTROL_CARD:
        errors.append("control_card: must match canonical producer control card")

    authority = payload.get("authority")
    if not isinstance(authority, dict):
        errors.append("authority: must be object")
    else:
        for key, expected in EXPECTED_AUTHORITY.items():
            if authority.get(key) is not expected:
                errors.append(f"authority.{key}: must be {expected!r}")

    inputs = payload.get("inputs")
    if not isinstance(inputs, dict):
        errors.append("inputs: must be object")
    else:
        for key in ("raw_archive", "output_json"):
            if not isinstance(inputs.get(key), str) or not inputs.get(key):
                errors.append(f"inputs.{key}: must be non-empty string")

    params = payload.get("parameters")
    if not isinstance(params, dict):
        errors.append("parameters: must be object")
    else:
        for key in ("frame", "frame_limit"):
            value = params.get(key)
            if value is not None and _nonnegative_int(value) is None:
                errors.append(f"parameters.{key}: must be null or nonnegative int")
        for key in ("top_k", "pool_multiplier"):
            value = _nonnegative_int(params.get(key))
            if value is None or value <= 0:
                errors.append(f"parameters.{key}: must be positive int")
        zero_eps = _finite_float(params.get("zero_eps"))
        if zero_eps is None or zero_eps <= 0.0:
            errors.append("parameters.zero_eps: must be finite positive")

    rows = payload.get("triad_phase_laplacian_rows")
    if not isinstance(rows, list) or not rows:
        errors.append("triad_phase_laplacian_rows: must be non-empty list")
        rows = []

    status_counts = {OK_STATUS: 0, PARTIAL_STATUS: 0, ERROR_STATUS: 0}
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            errors.append(f"triad_phase_laplacian_rows[{index}]: must be object")
            continue
        status = row.get("status")
        if status not in ALLOWED_STATUSES:
            errors.append(f"triad_phase_laplacian_rows[{index}].status: must be ok|partial|error")
        else:
            status_counts[str(status)] += 1
        if _nonnegative_int(row.get("frame")) is None:
            errors.append(f"triad_phase_laplacian_rows[{index}].frame: must be nonnegative int")
        for key in ("candidate_only", "empirical_non_promoting", "fail_closed"):
            if row.get(key) is not True:
                errors.append(f"triad_phase_laplacian_rows[{index}].{key}: must be true")
        if row.get("route_mode") != "fail-closed":
            errors.append(f"triad_phase_laplacian_rows[{index}].route_mode: must be 'fail-closed'")
        for key in ("selected_mode_count", "triad_count", "phase_graph_unsigned_laplacian_zero_eigen_count", "phase_graph_signed_laplacian_zero_eigen_count"):
            value = row.get(key)
            if value is not None and _nonnegative_int(value) is None:
                errors.append(f"triad_phase_laplacian_rows[{index}].{key}: must be nonnegative int or null")
        for key in (
            "mode_concentration_fraction",
            "selected_mode_amplitude_sum",
            "shell_radius_mean",
            "triad_negative_mass",
            "triad_negative_mass_ratio",
            "triad_phase_alignment_abs_mean",
            "triad_phase_alignment_mean",
            "triad_positive_mass",
            "triad_shell_spread_mean",
            "triad_shell_spread_p95",
            "triad_weight_mean",
            "triad_weight_p95",
            "triad_weight_sum",
            "phase_graph_signed_laplacian_trace",
            "phase_graph_signed_smallest_positive_eigenvalue_proxy",
            "phase_graph_stability_margin_proxy",
            "phase_graph_subunit_proxy",
            "phase_graph_unsigned_laplacian_spectral_gap_proxy",
            "phase_graph_unsigned_laplacian_trace",
        ):
            _check_numeric_or_null(
                row.get(key),
                f"triad_phase_laplacian_rows[{index}].{key}",
                errors,
                nonnegative=key != "triad_phase_alignment_mean",
            )
        if row.get("warnings") is not None and not isinstance(row.get("warnings"), list):
            errors.append(f"triad_phase_laplacian_rows[{index}].warnings: must be list or null")
        if row.get("errors") is not None and not isinstance(row.get("errors"), list):
            errors.append(f"triad_phase_laplacian_rows[{index}].errors: must be list or null")

    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
    else:
        processed_frames = _nonnegative_int(aggregate.get("processed_frames"))
        if processed_frames != len(rows):
            errors.append("aggregate.processed_frames: must match triad_phase_laplacian_rows length")
        for key, expected in (
            ("ok_frames", status_counts[OK_STATUS]),
            ("partial_frames", status_counts[PARTIAL_STATUS]),
            ("error_frames", status_counts[ERROR_STATUS]),
        ):
            if _nonnegative_int(aggregate.get(key)) != expected:
                errors.append(f"aggregate.{key}: must be {expected!r}")
        for key in (
            "top_k",
            "pool_multiplier",
            "selected_mode_count_mean",
            "triad_count_mean",
            "triad_count_total",
            "selected_mode_amplitude_sum_mean",
            "triad_weight_sum_mean",
            "phase_graph_unsigned_laplacian_trace_mean",
            "phase_graph_unsigned_laplacian_spectral_gap_proxy_mean",
            "phase_graph_signed_smallest_positive_eigenvalue_proxy_mean",
            "phase_graph_subunit_proxy_mean",
            "phase_graph_stability_margin_proxy_mean",
            "triad_negative_mass_ratio_mean",
            "phase_graph_negative_mass_ratio_mean",
            "triad_phase_alignment_mean",
            "zero_eps",
        ):
            _check_numeric_or_null(aggregate.get(key), f"aggregate.{key}", errors, nonnegative=key != "triad_phase_alignment_mean")
        for key in (
            "triad_count_vs_gap_correlation",
            "phase_graph_negative_mass_ratio_vs_gap_correlation",
            "phase_graph_negative_mass_ratio_vs_stability_correlation",
        ):
            value = aggregate.get(key)
            if value is not None:
                parsed = _finite_float(value)
                if parsed is None or parsed < -1.0 - 1.0e-12 or parsed > 1.0 + 1.0e-12:
                    errors.append(f"aggregate.{key}: correlation must lie in [-1,1]")

    return errors


def main() -> int:
    args = _parse_args()
    try:
        payload = _load_json(_input_path(args))
        errors = _check_payload(payload)
    except Exception as exc:  # noqa: BLE001
        errors = [str(exc)]

    receipt = {
        **CONTROL_CARD,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "route_mode": "fail-closed",
        "fail_closed": True,
        "ok": not errors,
        "status": OK_STATUS if not errors else ERROR_STATUS,
        "errors": errors,
        "warnings": [],
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(receipt, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(receipt, args.pretty))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
