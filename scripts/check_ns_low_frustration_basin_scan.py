#!/usr/bin/env python3
"""Validate ns_low_frustration_basin_scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_low_frustration_basin_scan.py"
CONTRACT = "check_ns_low_frustration_basin_scan"
SOURCE_CONTRACT = "ns_low_frustration_basin_scan"
SOURCE_SCRIPT = "scripts/ns_low_frustration_basin_scan.py"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_LOW_FRUSTRATION_BASIN_SCAN"
ROUTE_DECISION = "FAIL_CLOSED_NS_LOW_FRUSTRATION_BASIN_SCAN_CHECK"
SCHEMA_VERSION = "1.0.0"

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_low_frustration_basin_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_low_frustration_basin_scan_N128_20260621.json"
)

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}

SOURCE_CONTROL_CARD = {
    "O": "Empirically scan low-frustration basin occupancy around the best triad reference.",
    "R": (
        "Rebuild the selected-mode triad carrier, choose the best empirical reference, "
        "and probe how thin the low-frustration basin looks under perturbations."
    ),
    "C": SOURCE_SCRIPT,
    "S": "Candidate-only telemetry; basin occupancy and rarity proxies are empirical only.",
    "L": (
        "Load raw frames, reuse the selected Fourier-vorticity triad machinery, "
        "choose the best reference, and sample random plus structured perturbations around it."
    ),
    "P": SOURCE_ROUTE_DECISION,
    "G": "No theorem, Clay, residence-time exclusion, or promotion claim is inferred.",
    "F": "This scan estimates basin rarity only; it does not prove exclusion or closure.",
}

CONTROL_CARD = {
    "O": "Validate the low-frustration basin scan contract and receipt surface.",
    "R": "Check control card, authority flags, row metrics, and aggregate basin summaries.",
    "C": SCRIPT_NAME,
    "S": "Fail-closed checker: any schema drift, authority drift, or malformed metric is an error.",
    "L": "Load the scan JSON, validate row and aggregate surfaces, and emit a checker receipt.",
    "P": ROUTE_DECISION,
    "G": "Checker remains empirical and non-promoting.",
    "F": "The residence-time wall stays explicitly unproved; candidate-only telemetry is the only acceptable stance.",
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
    if not path.exists():
        raise FileNotFoundError(f"missing scan json: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"scan json must be an object: {path}")
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
    if value is None or isinstance(value, bool):
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
    if payload.get("script") != SOURCE_SCRIPT:
        errors.append(f"script: must be {SOURCE_SCRIPT!r}")
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
        for key in ("top_k", "pool_multiplier", "random_samples", "structured_grid", "seed"):
            value = _nonnegative_int(params.get(key))
            if value is None or value < 0:
                errors.append(f"parameters.{key}: must be nonnegative int")
        delta_bands = params.get("delta_bands")
        if not isinstance(delta_bands, list) or not delta_bands:
            errors.append("parameters.delta_bands: must be non-empty list")
        else:
            for index, item in enumerate(delta_bands):
                parsed = _finite_float(item)
                if parsed is None or parsed <= 0.0:
                    errors.append(f"parameters.delta_bands[{index}]: must be finite positive")
        zero_eps = _finite_float(params.get("zero_eps"))
        if zero_eps is None or zero_eps <= 0.0:
            errors.append("parameters.zero_eps: must be finite positive")

    rows = payload.get("low_frustration_basin_rows")
    if not isinstance(rows, list) or not rows:
        errors.append("low_frustration_basin_rows: must be non-empty list")
        rows = []

    status_counts = {OK_STATUS: 0, PARTIAL_STATUS: 0, ERROR_STATUS: 0}
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            errors.append(f"low_frustration_basin_rows[{index}]: must be object")
            continue
        status = row.get("status")
        if status not in ALLOWED_STATUSES:
            errors.append(f"low_frustration_basin_rows[{index}].status: must be ok|partial|error")
        else:
            status_counts[str(status)] += 1
        if _nonnegative_int(row.get("frame")) is None:
            errors.append(f"low_frustration_basin_rows[{index}].frame: must be nonnegative int")
        for key in ("candidate_only", "empirical_non_promoting"):
            if row.get(key) is not True:
                errors.append(f"low_frustration_basin_rows[{index}].{key}: must be true")
        if row.get("route_mode") != "fail-closed":
            errors.append(f"low_frustration_basin_rows[{index}].route_mode: must be 'fail-closed'")
        for key in ("selected_mode_count", "triad_count", "reference_candidate_count", "best_reference_rank", "best_global_reference_rank", "best_structured_reference_rank"):
            value = row.get(key)
            if value is not None and _nonnegative_int(value) is None:
                errors.append(f"low_frustration_basin_rows[{index}].{key}: must be nonnegative int or null")
        for key in (
            "selected_mode_amplitude_sum",
            "phase_field_fit_rmse",
            "zero_reference_floor_proxy",
            "zero_reference_floor_rmse",
            "best_reference_floor_proxy",
            "best_reference_floor_rmse",
            "best_reference_floor_p95",
            "best_global_floor_proxy",
            "best_structured_floor_proxy",
            "best_reference_floor_improvement_over_zero",
            "best_reference_floor_improvement_over_best_global",
            "best_structured_floor_improvement_over_best_global",
            "best_reference_phase_coherence",
            "best_reference_phase_alignment_fraction",
            "best_reference_phase_offset",
            "best_reference_phase_shift_rms",
            "best_reference_phase_slope",
            "negative_log_volume_proxy_mean",
            "basin_occupancy_mean",
            "pool_multiplier",
            "top_k",
            "zero_eps",
        ):
            _check_numeric_or_null(
                row.get(key),
                f"low_frustration_basin_rows[{index}].{key}",
                errors,
                nonnegative=key
                not in (
                    "best_reference_phase_offset",
                    "best_reference_phase_slope",
                    "best_reference_floor_improvement_over_best_global",
                    "best_structured_floor_improvement_over_best_global",
                ),
            )
        candidate_rows = row.get("reference_candidates")
        if candidate_rows is not None and not isinstance(candidate_rows, list):
            errors.append(f"low_frustration_basin_rows[{index}].reference_candidates: must be list or null")
        delta_rows = row.get("delta_band_rows")
        if delta_rows is not None and not isinstance(delta_rows, list):
            errors.append(f"low_frustration_basin_rows[{index}].delta_band_rows: must be list or null")
        if row.get("warnings") is not None and not isinstance(row.get("warnings"), list):
            errors.append(f"low_frustration_basin_rows[{index}].warnings: must be list or null")
        if row.get("errors") is not None and not isinstance(row.get("errors"), list):
            errors.append(f"low_frustration_basin_rows[{index}].errors: must be list or null")

    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
    else:
        if _nonnegative_int(aggregate.get("processed_frames")) != len(rows):
            errors.append("aggregate.processed_frames: must match low_frustration_basin_rows length")
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
            "random_samples",
            "structured_grid",
            "selected_mode_count_mean",
            "triad_count_mean",
            "zero_reference_floor_proxy_mean",
            "best_reference_floor_proxy_mean",
            "best_reference_floor_improvement_over_zero_mean",
            "basin_occupancy_mean",
            "basin_occupancy_median",
            "negative_log_volume_proxy_mean",
            "negative_log_volume_proxy_median",
            "phase_field_fit_rmse_mean",
            "best_reference_is_zero_fraction",
            "best_reference_is_structured_fraction",
            "best_reference_is_fitted_fraction",
            "zero_eps",
        ):
            _check_numeric_or_null(aggregate.get(key), f"aggregate.{key}", errors, nonnegative=True)
        for key in (
            "best_reference_floor_improvement_over_best_global_mean",
            "best_structured_floor_improvement_over_best_global_mean",
        ):
            _check_numeric_or_null(aggregate.get(key), f"aggregate.{key}", errors, nonnegative=False)
        for key in (
            "occupancy_vs_best_floor_correlation",
            "rarity_vs_best_floor_correlation",
            "best_floor_vs_zero_floor_correlation",
            "triad_count_vs_basin_occupancy_correlation",
        ):
            value = aggregate.get(key)
            if value is not None:
                parsed = _finite_float(value)
                if parsed is None or parsed < -1.0 - 1.0e-12 or parsed > 1.0 + 1.0e-12:
                    errors.append(f"aggregate.{key}: correlation must lie in [-1,1]")
        delta_rows = aggregate.get("delta_band_rows")
        if delta_rows is not None and not isinstance(delta_rows, list):
            errors.append("aggregate.delta_band_rows: must be list or null")

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
        "status": OK_STATUS if not errors else ERROR_STATUS,
        "ok": not errors,
        "authority": dict(EXPECTED_AUTHORITY),
        "errors": errors,
        "warnings": [],
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(receipt, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(receipt, args.pretty))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
