#!/usr/bin/env python3
"""Validate ns_triad_cycle_obstruction_scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_triad_cycle_obstruction_scan.py"
CONTRACT = "check_ns_triad_cycle_obstruction_scan"
SOURCE_CONTRACT = "ns_triad_cycle_obstruction_scan"
SOURCE_SCRIPT_NAME = "scripts/ns_triad_cycle_obstruction_scan.py"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_CYCLE_OBSTRUCTION_SCAN"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_CYCLE_OBSTRUCTION_SCAN_CHECK"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_cycle_obstruction_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_triad_cycle_obstruction_scan_N128_20260621.json"
)

SOURCE_CONTROL_CARD = {
    "O": "Measure candidate resonant-triad cycle obstruction telemetry on the raw N128 archive.",
    "R": (
        "Build a fail-closed triad carrier from dominant Fourier-vorticity modes, "
        "then summarize cycle-rank proxies and cocycle residue telemetry on the induced triad graph."
    ),
    "C": SOURCE_SCRIPT_NAME,
    "S": "Telemetry only; the cycle-obstruction carrier is empirical and non-promoting.",
    "L": (
        "Load raw frames, select dominant modes, form resonant selected-mode triads, "
        "and emit framewise cycle-obstruction metrics."
    ),
    "P": SOURCE_ROUTE_DECISION,
    "G": "No theorem, Clay, or route promotion is inferred from this scan.",
    "F": "A low cycle-rank proxy or low cocycle residue is still only empirical telemetry, not a proof.",
}

CONTROL_CARD = {
    "O": "Validate triad cycle-obstruction telemetry output.",
    "R": "Check control card, authority flags, fail-closed markers, obstruction metrics, and aggregate reconciliation.",
    "C": SCRIPT_NAME,
    "S": "Fail-closed checker for malformed triad cycle-obstruction telemetry surfaces.",
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


def _check_fraction(errors: list[str], path: str, value: Any) -> None:
    parsed = _finite_float(value)
    if parsed is None or parsed < -1.0e-12 or parsed > 1.0 + 1.0e-12:
        errors.append(f"{path}: must be finite fraction in [0,1]")


def _check_control_card(payload: dict[str, Any], errors: list[str]) -> None:
    nested_control_card = payload.get("control_card")
    if nested_control_card != SOURCE_CONTROL_CARD:
        errors.append("control_card: must exactly match the scan contract")


def _check_authority(payload: dict[str, Any], errors: list[str]) -> None:
    authority = payload.get("authority")
    if not isinstance(authority, dict):
        errors.append("authority: must be object")
        return
    for key, expected_value in EXPECTED_AUTHORITY.items():
        if authority.get(key) is not expected_value:
            errors.append(f"authority.{key}: must be {expected_value!r}")


def _check_optional_list(errors: list[str], path: str, value: Any) -> None:
    if value is not None and not isinstance(value, list):
        errors.append(f"{path}: must be list or null")


def _check_row(row: dict[str, Any], path: str, errors: list[str]) -> None:
    status = row.get("status")
    if status not in ALLOWED_STATUSES:
        errors.append(f"{path}.status: must be ok|partial|error")
    if _nonnegative_int(row.get("frame")) is None:
        errors.append(f"{path}.frame: must be nonnegative int")
    if _nonnegative_int(row.get("snapshot_index")) is None:
        errors.append(f"{path}.snapshot_index: must be nonnegative int")
    if _finite_float(row.get("orbit_phase")) is None:
        errors.append(f"{path}.orbit_phase: must be finite")
    if row.get("route_mode") != "fail-closed":
        errors.append(f"{path}.route_mode: must be 'fail-closed'")
    for key in ("candidate_only", "empirical_non_promoting"):
        if row.get(key) is not True:
            errors.append(f"{path}.{key}: must be true")
    if row.get("fail_closed") is not None and row.get("fail_closed") is not True:
        errors.append(f"{path}.fail_closed: if present must be true")

    if status == ERROR_STATUS:
        errors_list = row.get("errors")
        if not isinstance(errors_list, list) or not errors_list:
            errors.append(f"{path}.errors: error rows must have a non-empty errors list")

    for key in ("selected_mode_count", "carrier_mode_count", "triad_count", "cycle_rank_proxy"):
        if _nonnegative_int(row.get(key)) is None:
            errors.append(f"{path}.{key}: must be nonnegative int")
    for key in ("mode_graph_edge_count", "mode_graph_component_count"):
        value = row.get(key)
        if value is not None and _nonnegative_int(value) is None:
            errors.append(f"{path}.{key}: must be nonnegative int or null")

    for key in (
        "selected_mode_amplitude_sum",
        "triad_weight_sum",
        "triad_weight_mean",
        "triad_weight_p95",
        "cocycle_residue_rms",
        "cocycle_residue_max",
        "carrier_shell_radius_mean",
        "triad_shell_spread_mean",
        "triad_shell_spread_p95",
        "cycle_obstruction_density",
        "cycle_basis_proxy",
        "cycle_obstruction_score",
    ):
        value = _finite_float(row.get(key))
        if value is None:
            errors.append(f"{path}.{key}: must be finite")
        elif value < -1.0e-12:
            errors.append(f"{path}.{key}: must be nonnegative")

    for key in (
        "mode_concentration_fraction",
        "cocycle_exact_lock_fraction",
        "exact_lock_near_lock_fraction",
        "exact_lock_score",
    ):
        _check_fraction(errors, f"{path}.{key}", row.get(key))

    if row.get("dominant_mode_key") is not None and not isinstance(row.get("dominant_mode_key"), list):
        errors.append(f"{path}.dominant_mode_key: must be list or null")
    if row.get("selected_mode_keys") is not None and not isinstance(row.get("selected_mode_keys"), list):
        errors.append(f"{path}.selected_mode_keys: must be list or null")
    if row.get("triad_cycle_records") is not None and not isinstance(row.get("triad_cycle_records"), list):
        errors.append(f"{path}.triad_cycle_records: must be list or null")
    _check_optional_list(errors, f"{path}.warnings", row.get("warnings"))
    _check_optional_list(errors, f"{path}.errors", row.get("errors"))


def _check_aggregate(aggregate: dict[str, Any], row_count: int, errors: list[str]) -> None:
    processed_frames = _nonnegative_int(aggregate.get("processed_frames"))
    if processed_frames is None:
        errors.append("aggregate.processed_frames: must be nonnegative int")
        processed_frames = 0
    if processed_frames != row_count:
        errors.append("aggregate.processed_frames: must match row count")

    for key in ("ok_frames", "partial_frames", "error_frames"):
        if _nonnegative_int(aggregate.get(key)) is None:
            errors.append(f"aggregate.{key}: must be nonnegative int")

    if all(_nonnegative_int(aggregate.get(key)) is not None for key in ("ok_frames", "partial_frames", "error_frames")):
        total = (
            int(aggregate.get("ok_frames", 0))
            + int(aggregate.get("partial_frames", 0))
            + int(aggregate.get("error_frames", 0))
        )
        if total != processed_frames:
            errors.append("aggregate row status counts must sum to processed_frames")

    for key in ("top_k", "pool_multiplier"):
        value = _nonnegative_int(aggregate.get(key))
        if value is None or value <= 0:
            errors.append(f"aggregate.{key}: must be positive int")
    zero_eps = _finite_float(aggregate.get("zero_eps"))
    if zero_eps is None or zero_eps <= 0.0:
        errors.append("aggregate.zero_eps: must be finite positive")

    for key in (
        "selected_mode_count_mean",
        "triad_count_mean",
        "cycle_rank_proxy_mean",
        "selected_mode_amplitude_sum_mean",
        "triad_weight_sum_mean",
        "cocycle_residue_rms_mean",
        "cocycle_residue_max_mean",
        "carrier_mode_count_mean",
        "carrier_shell_radius_mean",
        "cycle_obstruction_density_mean",
        "cycle_basis_proxy_mean",
        "cycle_obstruction_score_mean",
        "exact_lock_score_mean",
    ):
        value = _finite_float(aggregate.get(key))
        if value is None:
            continue
        if value < -1.0e-12:
            errors.append(f"aggregate.{key}: must be nonnegative")

    for key in (
        "incidence_density_mean",
        "mode_concentration_fraction_mean",
    ):
        value = aggregate.get(key)
        if value is not None:
            _check_fraction(errors, f"aggregate.{key}", value)

    for key in (
        "cycle_obstruction_vs_exact_lock_correlation",
        "cycle_rank_vs_residue_correlation",
        "residue_vs_concentration_correlation",
    ):
        value = aggregate.get(key)
        if value is not None:
            parsed = _finite_float(value)
            if parsed is None or parsed < -1.0 - 1.0e-12 or parsed > 1.0 + 1.0e-12:
                errors.append(f"aggregate.{key}: must be null or finite in [-1,1]")


def _check_payload(payload: dict[str, Any]) -> list[str]:
    errors: list[str] = []

    _check_control_card(payload, errors)
    if payload.get("contract") != SOURCE_CONTRACT:
        errors.append(f"contract: must be {SOURCE_CONTRACT!r}")
    if payload.get("route_decision") != SOURCE_ROUTE_DECISION:
        errors.append(f"route_decision: must be {SOURCE_ROUTE_DECISION!r}")
    if payload.get("schema_version") != SCHEMA_VERSION:
        errors.append(f"schema_version: must be {SCHEMA_VERSION!r}")
    if payload.get("script") != SOURCE_SCRIPT_NAME:
        errors.append(f"script: must be {SOURCE_SCRIPT_NAME!r}")
    if payload.get("status") not in ALLOWED_STATUSES:
        errors.append(f"status: must be one of {sorted(ALLOWED_STATUSES)!r}")
    if payload.get("route_mode") is not None and payload.get("route_mode") != "fail-closed":
        errors.append("route_mode: if present must be 'fail-closed'")
    if payload.get("fail_closed") is not None and payload.get("fail_closed") is not True:
        errors.append("fail_closed: if present must be true")
    if payload.get("ok") is not None and payload.get("ok") not in (True, False):
        errors.append("ok: if present must be bool")

    _check_authority(payload, errors)

    inputs = payload.get("inputs")
    if inputs is not None and not isinstance(inputs, dict):
        errors.append("inputs: must be object or null")
    elif isinstance(inputs, dict):
        for key in ("raw_archive", "output_json"):
            if not isinstance(inputs.get(key), str) or not inputs.get(key):
                errors.append(f"inputs.{key}: must be non-empty string")

    params = payload.get("parameters")
    if params is not None and not isinstance(params, dict):
        errors.append("parameters: must be object or null")
    elif isinstance(params, dict):
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
        if "lock_eps" in params:
            lock_eps = _finite_float(params.get("lock_eps"))
            if lock_eps is None or lock_eps <= 0.0:
                errors.append("parameters.lock_eps: must be finite positive")

    rows = payload.get("triad_cycle_obstruction_rows")
    if not isinstance(rows, list) or not rows:
        errors.append("triad_cycle_obstruction_rows: must be non-empty list")
        rows = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            errors.append(f"triad_cycle_obstruction_rows[{index}]: must be object")
            continue
        status = row.get("status")
        if status not in ALLOWED_STATUSES:
            errors.append(f"triad_cycle_obstruction_rows[{index}].status: must be ok|partial|error")
        _check_row(row, f"triad_cycle_obstruction_rows[{index}]", errors)

    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
        aggregate = {}
    _check_aggregate(aggregate, len(rows), errors)

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
