#!/usr/bin/env python3
"""Validate ns_triad_frustration_defect_scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_triad_frustration_defect_scan.py"
CONTRACT = "check_ns_triad_frustration_defect_scan"
SOURCE_CONTRACT = "ns_triad_frustration_defect_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_FRUSTRATION_DEFECT_SCAN_CHECK"
SOURCE_SCRIPT_NAME = "scripts/ns_triad_frustration_defect_scan.py"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}
EXPECTED_CONTROL_CARD = {
    "O": "Measure candidate triad phase-frustration telemetry on the raw N128 archive.",
    "R": (
        "Build resonant selected-mode triads, fit a low-dimensional phase field, "
        "and summarize weighted phase-closure frustration together with coherence-loss proxies."
    ),
    "C": SOURCE_SCRIPT_NAME,
    "S": "Empirical scan only; malformed inputs and non-finite arithmetic are fail-closed errors.",
    "L": (
        "Load raw frames, select dominant modes, construct resonant triads, "
        "fit a finite-dimensional phase field, and emit framewise plus aggregate telemetry."
    ),
    "P": "FAIL_CLOSED_NS_TRIAD_FRUSTRATION_DEFECT_SCAN",
    "G": "No theorem, Clay, or promotion claim is inferred from this scan.",
    "F": "All outputs are candidate-only empirical telemetry and remain non-promoting.",
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

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_frustration_defect_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_triad_frustration_defect_scan_N128_20260621.json"
)

CONTROL_CARD = {
    "O": "Validate triad frustration defect telemetry output.",
    "R": "Check schema, authority flags, route markers, row counts, and finite candidate-only triad metrics.",
    "C": SCRIPT_NAME,
    "S": "Fail-closed checker for malformed triad-frustration telemetry surfaces.",
    "L": "Load the scan JSON, validate rows and aggregates, then emit a checker receipt.",
    "P": ROUTE_DECISION,
    "G": "Checker remains empirical and non-promoting.",
    "F": "Any malformed field, authority drift, or route-marker mismatch is a hard error.",
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


def _check_control_card(payload: dict[str, Any], errors: list[str]) -> None:
    control_card = {key: payload.get(key) for key in ("O", "R", "C", "S", "L", "P", "G", "F")}
    if control_card != EXPECTED_CONTROL_CARD:
        errors.append("control card fields must exactly match the scan contract")
    nested_control_card = payload.get("control_card")
    if nested_control_card != EXPECTED_CONTROL_CARD:
        errors.append("control_card: must exactly match the scan contract")


def _check_authority(payload: dict[str, Any], errors: list[str]) -> None:
    authority = payload.get("authority")
    if authority != EXPECTED_AUTHORITY:
        errors.append("authority: must be object")
        return


def _check_row(row: dict[str, Any], path: str, errors: list[str]) -> None:
    status = row.get("status")
    if _nonnegative_int(row.get("frame")) is None:
        errors.append(f"{path}.frame: must be nonnegative int")
    if _nonnegative_int(row.get("snapshot_index")) is None:
        errors.append(f"{path}.snapshot_index: must be nonnegative int")
    if _finite_float(row.get("orbit_phase")) is None:
        errors.append(f"{path}.orbit_phase: must be finite")
    if row.get("route_mode") != "fail-closed":
        errors.append(f"{path}.route_mode: must be 'fail-closed'")
    if row.get("candidate_only") is not True:
        errors.append(f"{path}.candidate_only: must be true")
    if row.get("empirical_non_promoting") is not True:
        errors.append(f"{path}.empirical_non_promoting: must be true")
    if status not in ALLOWED_STATUSES:
        errors.append(f"{path}.status: must be ok|partial|error")
    if status == ERROR_STATUS:
        errors_list = row.get("errors")
        if not isinstance(errors_list, list) or not errors_list:
            errors.append(f"{path}.errors: error rows must have a non-empty errors list")
    else:
        for key in (
            "selected_mode_amplitude_sum",
            "selected_mode_count",
            "triad_count",
        ):
            if _nonnegative_int(row.get(key)) is None:
                if key == "selected_mode_amplitude_sum":
                    if _finite_float(row.get(key)) is None or _finite_float(row.get(key)) < -1.0e-12:
                        errors.append(f"{path}.{key}: must be finite and nonnegative")
                else:
                    errors.append(f"{path}.{key}: must be nonnegative int")
        for key in (
            "selected_mode_amplitude_sum",
            "triad_weight_sum",
            "triad_weight_mean",
            "triad_weight_p95",
            "triad_weight_concentration",
            "triad_weight_entropy_normalized",
            "triad_effective_count",
            "triad_phase_coherence",
            "coherence_loss_proxy",
            "frustration_residual_mean",
            "frustration_residual_rmse",
            "frustration_residual_p95",
            "triad_shell_spread_mean",
            "triad_shell_spread_p95",
            "mode_concentration_fraction",
            "phase_field_fit_rmse",
            "triad_weight_per_mode",
            "triad_effective_fraction_of_selected_modes",
            "frustration_density",
        ):
            value = _finite_float(row.get(key))
            if value is None:
                errors.append(f"{path}.{key}: must be finite")
            elif key in {
                "triad_weight_concentration",
                "triad_weight_entropy_normalized",
                "triad_phase_coherence",
                "coherence_loss_proxy",
                "mode_concentration_fraction",
                "triad_effective_fraction_of_selected_modes",
            } and (value < -1.0e-12 or value > 1.0 + 1.0e-12):
                errors.append(f"{path}.{key}: must lie in [0,1]")
            elif key == "triad_weight_entropy_normalized" and value < -1.0e-12:
                errors.append(f"{path}.{key}: must be nonnegative")
            elif key in {"triad_effective_count", "triad_weight_sum", "triad_weight_mean", "triad_weight_p95", "triad_weight_per_mode", "phase_field_fit_rmse", "frustration_residual_mean", "frustration_residual_rmse", "frustration_residual_p95", "triad_shell_spread_mean", "triad_shell_spread_p95", "frustration_density"} and value < -1.0e-12:
                errors.append(f"{path}.{key}: must be nonnegative")
    if row.get("warnings") is not None and not isinstance(row.get("warnings"), list):
        errors.append(f"{path}.warnings: must be list or null")
    if row.get("errors") is not None and not isinstance(row.get("errors"), list):
        errors.append(f"{path}.errors: must be list or null")


def main() -> int:
    args = _parse_args()
    errors: list[str] = []
    warnings: list[str] = []
    try:
        payload = _load_json(_input_path(args))
    except Exception as exc:  # noqa: BLE001
        receipt = {
            **CONTROL_CARD,
            "contract": CONTRACT,
            "route_decision": ROUTE_DECISION,
            "route_mode": "fail-closed",
            "fail_closed": True,
            "status": ERROR_STATUS,
            "ok": False,
            "errors": [str(exc)],
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(receipt, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(receipt, args.pretty))
        return 1

    _check_control_card(payload, errors)
    if payload.get("contract") != SOURCE_CONTRACT:
        errors.append(f"contract: must be {SOURCE_CONTRACT!r}")
    if payload.get("route_decision") != "FAIL_CLOSED_NS_TRIAD_FRUSTRATION_DEFECT_SCAN":
        errors.append("route_decision: must match the scan fail-closed marker")
    if payload.get("route_mode") != "fail-closed":
        errors.append("route_mode: must be 'fail-closed'")
    if payload.get("fail_closed") is not True:
        errors.append("fail_closed: must be true")
    if payload.get("schema_version") != "1.0.0":
        errors.append("schema_version: must be '1.0.0'")
    if payload.get("script") != SOURCE_SCRIPT_NAME:
        errors.append(f"script: must be {SOURCE_SCRIPT_NAME!r}")
    if payload.get("status") not in ALLOWED_STATUSES:
        errors.append("status: must be ok|partial|error")
    if payload.get("warnings") is not None and not isinstance(payload.get("warnings"), list):
        errors.append("warnings: must be list or null")
    if payload.get("errors") is not None and not isinstance(payload.get("errors"), list):
        errors.append("errors: must be list or null")
    _check_authority(payload, errors)

    rows = payload.get("triad_frustration_rows")
    if not isinstance(rows, list) or not rows:
        errors.append("triad_frustration_rows: must be non-empty list")
        rows = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            errors.append(f"triad_frustration_rows[{index}]: must be object")
            continue
        _check_row(row, f"triad_frustration_rows[{index}]", errors)

    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
        aggregate = {}
    processed = _nonnegative_int(aggregate.get("processed_frames"))
    if processed is None:
        errors.append("aggregate.processed_frames: must be nonnegative int")
        processed = 0
    ok_frames = _nonnegative_int(aggregate.get("ok_frames"))
    if ok_frames is None:
        errors.append("aggregate.ok_frames: must be nonnegative int")
        ok_frames = 0
    partial_frames = _nonnegative_int(aggregate.get("partial_frames"))
    if partial_frames is None:
        errors.append("aggregate.partial_frames: must be nonnegative int")
        partial_frames = 0
    error_frames = _nonnegative_int(aggregate.get("error_frames"))
    if error_frames is None:
        errors.append("aggregate.error_frames: must be nonnegative int")
        error_frames = 0
    if processed != len(rows):
        errors.append("aggregate.processed_frames: must equal triad_frustration_rows length")
    if processed != ok_frames + partial_frames + error_frames:
        errors.append("aggregate frame counts must sum to processed_frames")
    for key in (
        "selected_mode_count_mean",
        "triad_count_mean",
        "triad_count_total",
        "triad_weight_sum_mean",
        "triad_weight_concentration_mean",
        "triad_weight_entropy_normalized_mean",
        "triad_effective_count_mean",
        "triad_phase_coherence_mean",
        "coherence_loss_proxy_mean",
        "frustration_residual_mean",
        "frustration_residual_rmse_mean",
        "frustration_residual_p95_mean",
        "phase_field_fit_rmse_mean",
        "mode_concentration_fraction_mean",
        "triad_shell_spread_mean",
        "triad_shell_spread_p95_mean",
        "triad_weight_per_mode_mean",
        "effective_fraction_of_selected_modes_mean",
        "frustration_density_mean",
    ):
        value = _finite_float(aggregate.get(key))
        if value is None:
            errors.append(f"aggregate.{key}: must be finite")
        elif key in {
            "triad_weight_concentration_mean",
            "triad_weight_entropy_normalized_mean",
            "triad_phase_coherence_mean",
            "coherence_loss_proxy_mean",
            "mode_concentration_fraction_mean",
            "effective_fraction_of_selected_modes_mean",
        } and (value < -1.0e-12 or value > 1.0 + 1.0e-12):
            errors.append(f"aggregate.{key}: must lie in [0,1]")
        elif key in {
            "selected_mode_count_mean",
            "triad_count_mean",
            "phase_field_fit_rmse_mean",
            "triad_effective_count_mean",
            "triad_weight_sum_mean",
            "triad_weight_concentration_mean",
            "triad_weight_entropy_normalized_mean",
            "triad_shell_spread_mean",
            "triad_shell_spread_p95_mean",
            "triad_weight_per_mode_mean",
            "frustration_density_mean",
        } and value < -1.0e-12:
            errors.append(f"aggregate.{key}: must be nonnegative")

    if _nonnegative_int(aggregate.get("triad_count_total")) is None:
        errors.append("aggregate.triad_count_total: must be nonnegative int")

    for key in (
        "frustration_vs_coherence_loss_correlation",
        "triad_weight_vs_frustration_correlation",
    ):
        value = aggregate.get(key)
        if value is not None:
            parsed = _finite_float(value)
            if parsed is None or parsed < -1.0 - 1.0e-12 or parsed > 1.0 + 1.0e-12:
                errors.append(f"aggregate.{key}: must be null or finite in [-1,1]")

    ok = not errors
    receipt = {
        **CONTROL_CARD,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "route_mode": "fail-closed",
        "fail_closed": True,
        "scan_contract": payload.get("contract"),
        "scan_route_decision": payload.get("route_decision"),
        "scan_route_mode": payload.get("route_mode"),
        "status": OK_STATUS if ok else ERROR_STATUS,
        "ok": ok,
        "warnings": warnings,
        "errors": errors,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(receipt, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(receipt, args.pretty))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
