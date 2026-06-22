#!/usr/bin/env python3
"""Validate ns_triad_low_frustration_hessian_scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_triad_low_frustration_hessian_scan.py"
CONTRACT = "check_ns_triad_low_frustration_hessian_scan"
SOURCE_CONTRACT = "ns_triad_low_frustration_hessian_scan"
SOURCE_SCRIPT_NAME = "scripts/ns_triad_low_frustration_hessian_scan.py"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_LOW_FRUSTRATION_HESSIAN_SCAN"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_LOW_FRUSTRATION_HESSIAN_SCAN_CHECK"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_low_frustration_hessian_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_triad_low_frustration_hessian_scan_N128_20260621.json"
)

SOURCE_CONTROL_CARD = {
    "O": "Empirically scan low-frustration triad Hessian telemetry around the best triad reference.",
    "R": (
        "Rebuild the selected-mode triad carrier, evaluate Hessian-based basin proxies, "
        "and probe how thin the low-frustration basin looks under perturbations."
    ),
    "C": SOURCE_SCRIPT_NAME,
    "S": "Candidate-only telemetry; Hessian norms and basin proxies are empirical only.",
    "L": (
        "Load raw frames, reuse the selected Fourier-vorticity triad machinery, choose the best "
        "reference, and sample random plus structured perturbations around it."
    ),
    "P": SOURCE_ROUTE_DECISION,
    "G": "No theorem, Clay, residence-time exclusion, or promotion claim is inferred.",
    "F": "This scan estimates Hessian-based basin structure only; it does not prove exclusion or closure.",
}

CONTROL_CARD = {
    "O": "Validate the low-frustration triad Hessian scan contract and receipt surface.",
    "R": "Check control card, authority flags, row metrics, and aggregate Hessian summaries.",
    "C": SCRIPT_NAME,
    "S": "Fail-closed checker: any schema drift, authority drift, or malformed metric is an error.",
    "L": "Load the scan JSON, validate row and aggregate surfaces, and emit a checker receipt.",
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


def _check_fraction_or_null(value: Any, path: str, errors: list[str]) -> None:
    parsed = _finite_float(value)
    if parsed is None:
        if value is not None:
            errors.append(f"{path}: must be finite or null")
        return
    if parsed < -1.0e-12 or parsed > 1.0 + 1.0e-12:
        errors.append(f"{path}: must lie in [0,1]")


def _check_control_card(payload: dict[str, Any], errors: list[str]) -> None:
    for key, expected_value in SOURCE_CONTROL_CARD.items():
        if payload.get(key) != expected_value:
            errors.append(f"{key}: must be {expected_value!r}")
    control_card = payload.get("control_card")
    if control_card != SOURCE_CONTROL_CARD:
        errors.append("control_card: must match canonical producer control card")


def _check_authority(payload: dict[str, Any], errors: list[str]) -> None:
    authority = payload.get("authority")
    if not isinstance(authority, dict):
        errors.append("authority: must be object")
        return
    for key, expected in EXPECTED_AUTHORITY.items():
        if authority.get(key) is not expected:
            errors.append(f"authority.{key}: must be {expected!r}")


def _check_row(row: dict[str, Any], path: str, errors: list[str]) -> None:
    status = row.get("status")
    if status not in ALLOWED_STATUSES:
        errors.append(f"{path}.status: must be ok|partial|error")
    if _nonnegative_int(row.get("frame")) is None:
        errors.append(f"{path}.frame: must be nonnegative int")
    if row.get("candidate_only") is not True:
        errors.append(f"{path}.candidate_only: must be true")
    if row.get("empirical_non_promoting") is not True:
        errors.append(f"{path}.empirical_non_promoting: must be true")
    if row.get("route_mode") != "fail-closed":
        errors.append(f"{path}.route_mode: must be 'fail-closed'")
    if row.get("best_reference_is_zero") not in (True, False):
        errors.append(f"{path}.best_reference_is_zero: must be boolean")
    if row.get("best_reference_is_structured") not in (True, False):
        errors.append(f"{path}.best_reference_is_structured: must be boolean")
    if row.get("best_reference_is_fitted") not in (True, False):
        errors.append(f"{path}.best_reference_is_fitted: must be boolean")

    for key in (
        "selected_mode_count",
        "triad_count",
        "reference_candidate_count",
        "best_reference_rank",
        "best_global_reference_rank",
        "best_structured_reference_rank",
    ):
        value = row.get(key)
        if value is not None and _nonnegative_int(value) is None:
            errors.append(f"{path}.{key}: must be nonnegative int or null")

    for key in (
        "selected_mode_amplitude_sum",
        "phase_field_fit_rmse",
        "zero_reference_hessian_proxy",
        "zero_reference_hessian_rmse",
        "best_reference_hessian_proxy",
        "best_reference_hessian_rmse",
        "best_reference_hessian_p95",
        "best_global_hessian_proxy",
        "best_structured_hessian_proxy",
        "best_reference_hessian_improvement_over_zero",
        "best_reference_hessian_improvement_over_best_global",
        "best_structured_hessian_improvement_over_best_global",
        "best_reference_phase_coherence",
        "best_reference_phase_alignment_fraction",
        "best_reference_phase_offset",
        "best_reference_phase_shift_rms",
        "best_reference_phase_slope",
        "negative_log_volume_proxy",
        "basin_occupancy_mean",
        "top_k",
        "pool_multiplier",
        "zero_eps",
    ):
        value = row.get(key)
        if key in {"best_reference_phase_offset", "best_reference_phase_slope"}:
            _check_numeric_or_null(value, f"{path}.{key}", errors, nonnegative=False)
        elif key in {
            "best_reference_hessian_improvement_over_zero",
            "best_reference_hessian_improvement_over_best_global",
            "best_structured_hessian_improvement_over_best_global",
            "best_reference_phase_offset",
            "best_reference_phase_slope",
        }:
            _check_numeric_or_null(value, f"{path}.{key}", errors, nonnegative=False)
        else:
            _check_numeric_or_null(value, f"{path}.{key}", errors, nonnegative=True)

    for key in (
        "best_reference_phase_coherence",
        "best_reference_phase_alignment_fraction",
        "basin_occupancy_mean",
    ):
        _check_fraction_or_null(row.get(key), f"{path}.{key}", errors)

    candidate_rows = row.get("reference_candidates")
    if candidate_rows is not None and not isinstance(candidate_rows, list):
        errors.append(f"{path}.reference_candidates: must be list or null")
    delta_rows = row.get("delta_band_rows")
    if delta_rows is not None and not isinstance(delta_rows, list):
        errors.append(f"{path}.delta_band_rows: must be list or null")
    if row.get("warnings") is not None and not isinstance(row.get("warnings"), list):
        errors.append(f"{path}.warnings: must be list or null")
    if row.get("errors") is not None and not isinstance(row.get("errors"), list):
        errors.append(f"{path}.errors: must be list or null")
    if status == ERROR_STATUS:
        errors_list = row.get("errors")
        if not isinstance(errors_list, list) or not errors_list:
            errors.append(f"{path}.errors: error rows must have a non-empty errors list")


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

    _check_control_card(payload, errors)
    _check_authority(payload, errors)

    inputs = payload.get("inputs")
    if not isinstance(inputs, dict):
        errors.append("inputs: must be object")
    else:
        for key in ("raw_archive", "output_json"):
            if not isinstance(inputs.get(key), str) or not inputs.get(key):
                errors.append(f"inputs.{key}: must be non-empty string")
        for key in ("frame", "frame_limit", "top_k", "pool_multiplier", "random_samples", "structured_grid", "seed"):
            value = inputs.get(key)
            if value is not None and _nonnegative_int(value) is None:
                errors.append(f"inputs.{key}: must be null or nonnegative int")
        if "zero_eps" in inputs:
            _check_numeric_or_null(inputs.get("zero_eps"), "inputs.zero_eps", errors, nonnegative=True)

    parameters = payload.get("parameters")
    if parameters is not None and not isinstance(parameters, dict):
        errors.append("parameters: must be object or null")
    elif isinstance(parameters, dict):
        for key in ("frame", "frame_limit", "top_k", "pool_multiplier", "random_samples", "structured_grid", "seed"):
            value = parameters.get(key)
            if value is not None and _nonnegative_int(value) is None:
                errors.append(f"parameters.{key}: must be null or nonnegative int")
        if "zero_eps" in parameters:
            _check_numeric_or_null(parameters.get("zero_eps"), "parameters.zero_eps", errors, nonnegative=True)
        if "delta_bands" in parameters:
            delta_bands = parameters.get("delta_bands")
            if not isinstance(delta_bands, list) or not delta_bands:
                errors.append("parameters.delta_bands: must be non-empty list")
            else:
                for index, value in enumerate(delta_bands):
                    parsed = _finite_float(value)
                    if parsed is None or parsed <= 0.0:
                        errors.append(f"parameters.delta_bands[{index}]: must be finite positive")

    rows = payload.get("low_frustration_hessian_rows")
    if not isinstance(rows, list) or not rows:
        errors.append("low_frustration_hessian_rows: must be non-empty list")
        rows = []
    status_counts = {OK_STATUS: 0, PARTIAL_STATUS: 0, ERROR_STATUS: 0}
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            errors.append(f"low_frustration_hessian_rows[{index}]: must be object")
            continue
        status = row.get("status")
        if status in status_counts:
            status_counts[str(status)] += 1
        _check_row(row, f"low_frustration_hessian_rows[{index}]", errors)

    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
        aggregate = {}
    else:
        processed = _nonnegative_int(aggregate.get("processed_frames"))
        if processed is None:
            errors.append("aggregate.processed_frames: must be nonnegative int")
            processed = 0
        if processed != len(rows):
            errors.append("aggregate.processed_frames: must match low_frustration_hessian_rows length")

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
            "zero_reference_hessian_proxy_mean",
            "best_reference_hessian_proxy_mean",
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
            if key in {"basin_occupancy_mean", "basin_occupancy_median", "best_reference_is_zero_fraction", "best_reference_is_structured_fraction", "best_reference_is_fitted_fraction"}:
                _check_fraction_or_null(aggregate.get(key), f"aggregate.{key}", errors)
            elif key in {"selected_mode_count_mean", "triad_count_mean", "phase_field_fit_rmse_mean", "zero_reference_hessian_proxy_mean", "best_reference_hessian_proxy_mean", "negative_log_volume_proxy_mean", "negative_log_volume_proxy_median"}:
                _check_numeric_or_null(aggregate.get(key), f"aggregate.{key}", errors, nonnegative=True)
            else:
                _check_numeric_or_null(aggregate.get(key), f"aggregate.{key}", errors, nonnegative=True)

        for key in (
            "best_reference_hessian_improvement_over_zero_mean",
            "best_reference_hessian_improvement_over_best_global_mean",
            "best_structured_hessian_improvement_over_best_global_mean",
        ):
            _check_numeric_or_null(aggregate.get(key), f"aggregate.{key}", errors, nonnegative=False)

        for key in (
            "occupancy_vs_best_reference_hessian_correlation",
            "rarity_vs_best_reference_hessian_correlation",
            "best_reference_vs_zero_hessian_correlation",
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
    path = _input_path(args)
    errors: list[str] = []
    warnings: list[str] = []
    try:
        payload = _load_json(path)
        errors = _check_payload(payload)
    except Exception as exc:  # noqa: BLE001
        errors = [str(exc)]

    receipt = {
        **CONTROL_CARD,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "route_mode": "fail-closed",
        "fail_closed": True,
        "scan_contract": payload.get("contract") if "payload" in locals() and isinstance(payload, dict) else None,
        "scan_route_decision": payload.get("route_decision") if "payload" in locals() and isinstance(payload, dict) else None,
        "scan_route_mode": payload.get("route_mode") if "payload" in locals() and isinstance(payload, dict) else None,
        "schema_version": SCHEMA_VERSION,
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
