#!/usr/bin/env python3
"""Validate ns_triad_incidence_cocycle_scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_triad_incidence_cocycle_scan.py"
CONTRACT = "check_ns_triad_incidence_cocycle_scan"
SOURCE_CONTRACT = "ns_triad_incidence_cocycle_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_INCIDENCE_COCYCLE_SCAN_CHECK"
SCAN_ROUTE_DECISION = ROUTE_DECISION.replace("_CHECK", "")
EXPECTED_SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_incidence_cocycle_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_triad_incidence_cocycle_scan_N128_20260621.json"
)

CONTROL_CARD = {
    "O": "Validate triad incidence and cocycle telemetry output.",
    "R": "Check the schema, authority flags, row counts, incidence records, and cycle proxies.",
    "C": SCRIPT_NAME,
    "S": "Fail-closed checker for malformed incidence/cycle telemetry surfaces.",
    "L": "Load the scan JSON, validate rows and aggregates, then emit a checker receipt.",
    "P": ROUTE_DECISION,
    "G": "Checker remains empirical and non-promoting.",
    "F": "Any malformed field, invalid proxy, or authority drift is a hard error.",
}

SOURCE_CONTROL_CARD = {
    "O": "Measure candidate resonant-triad incidence and cocycle telemetry on the raw N128 archive.",
    "R": (
        "Build a fail-closed carrier from dominant Fourier-vorticity modes, extract resonant selected-mode triads, "
        "assemble an incidence-style triad graph, and track cycle-rank and exact-lock proxies."
    ),
    "C": "scripts/ns_triad_incidence_cocycle_scan.py",
    "S": "Telemetry only; the incidence/cycle carrier is empirical and non-promoting.",
    "L": (
        "Load raw frames, construct a dominant mode carrier, form resonant triads, "
        "build incidence records, and emit framewise cocycle metrics."
    ),
    "P": "FAIL_CLOSED_NS_TRIAD_INCIDENCE_COCYCLE_SCAN",
    "G": "No theorem, Clay, or route promotion is inferred from this scan.",
    "F": "A low residual or low cycle rank is still only empirical telemetry, not a proof of solvability or promotion.",
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
    for key, expected_value in SOURCE_CONTROL_CARD.items():
        if payload.get(key) != expected_value:
            errors.append(f"{key}: must be {expected_value!r}")


def _check_nested_control_card(payload: dict[str, Any], errors: list[str]) -> None:
    control_card = payload.get("control_card")
    if not isinstance(control_card, dict):
        errors.append("control_card: must be object")
        return
    for key, expected_value in SOURCE_CONTROL_CARD.items():
        if control_card.get(key) != expected_value:
            errors.append(f"control_card.{key}: must be {expected_value!r}")


def _check_authority(payload: dict[str, Any], errors: list[str]) -> None:
    authority = payload.get("authority")
    if not isinstance(authority, dict):
        errors.append("authority: must be object")
        return
    expected = {
        "candidate_only": True,
        "empirical_non_promoting": True,
        "truth_authority": False,
        "theorem_authority": False,
        "clay_authority": False,
        "runtime_authority": False,
        "promoted": False,
    }
    for key, expected_value in expected.items():
        if authority.get(key) is not expected_value:
            errors.append(f"authority.{key}: must be {expected_value!r}")


def _check_incidence_record(record: dict[str, Any], path: str, errors: list[str]) -> None:
    mode_indices = record.get("mode_indices")
    if not isinstance(mode_indices, list) or len(mode_indices) != 3:
        errors.append(f"{path}.mode_indices: must be list of length 3")
    else:
        for index, value in enumerate(mode_indices):
            if _nonnegative_int(value) is None:
                errors.append(f"{path}.mode_indices[{index}]: must be nonnegative int")

    mode_keys = record.get("mode_keys")
    if not isinstance(mode_keys, list) or len(mode_keys) != 3:
        errors.append(f"{path}.mode_keys: must be list of length 3")

    incidence_signs = record.get("incidence_signs")
    if not isinstance(incidence_signs, list) or len(incidence_signs) != 3:
        errors.append(f"{path}.incidence_signs: must be list of length 3")
    else:
        if incidence_signs != [1, 1, -1]:
            errors.append(f"{path}.incidence_signs: must be [1,1,-1]")

    for key in ("weight", "phase_mismatch", "abs_phase_mismatch"):
        value = _finite_float(record.get(key))
        if value is None:
            errors.append(f"{path}.{key}: must be finite")
        elif key != "phase_mismatch" and value < 0.0:
            errors.append(f"{path}.{key}: must be nonnegative")

    if record.get("exact_lock_hit") not in (True, False):
        errors.append(f"{path}.exact_lock_hit: must be boolean")


def main() -> int:
    args = _parse_args()
    path = _input_path(args)
    errors: list[str] = []
    warnings: list[str] = []
    try:
        payload = _load_json(path)
    except Exception as exc:  # noqa: BLE001
        receipt = {
            **CONTROL_CARD,
            "contract": CONTRACT,
            "route_decision": ROUTE_DECISION,
            "status": ERROR_STATUS,
            "ok": False,
            "errors": [str(exc)],
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(receipt, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(receipt, args.pretty))
        return 1

    _check_control_card(payload, errors)
    _check_nested_control_card(payload, errors)
    if payload.get("contract") != SOURCE_CONTRACT:
        errors.append(f"contract: must be {SOURCE_CONTRACT!r}")
    if payload.get("route_decision") != SCAN_ROUTE_DECISION:
        errors.append(f"route_decision: must be {SCAN_ROUTE_DECISION!r}")
    if payload.get("script") != "scripts/ns_triad_incidence_cocycle_scan.py":
        errors.append("script: must be scripts/ns_triad_incidence_cocycle_scan.py")
    if payload.get("schema_version") != EXPECTED_SCHEMA_VERSION:
        errors.append(f"schema_version: must be {EXPECTED_SCHEMA_VERSION!r}")
    if payload.get("status") not in ALLOWED_STATUSES:
        errors.append(f"status: must be one of {sorted(ALLOWED_STATUSES)!r}")
    _check_authority(payload, errors)

    rows = payload.get("triad_incidence_rows")
    if not isinstance(rows, list) or not rows:
        errors.append("triad_incidence_rows: must be non-empty list")
        rows = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            errors.append(f"triad_incidence_rows[{index}]: must be object")
            continue
        if row.get("status") not in ALLOWED_STATUSES:
            errors.append(f"triad_incidence_rows[{index}].status: invalid status")
        if _nonnegative_int(row.get("frame")) is None:
            errors.append(f"triad_incidence_rows[{index}].frame: must be nonnegative int")
        if _nonnegative_int(row.get("snapshot_index")) is None:
            errors.append(f"triad_incidence_rows[{index}].snapshot_index: must be nonnegative int")
        if _finite_float(row.get("orbit_phase")) is None:
            errors.append(f"triad_incidence_rows[{index}].orbit_phase: must be finite")
        if _nonnegative_int(row.get("mode_count")) is None:
            errors.append(f"triad_incidence_rows[{index}].mode_count: must be nonnegative int")
        if _nonnegative_int(row.get("carrier_mode_count")) is None:
            errors.append(f"triad_incidence_rows[{index}].carrier_mode_count: must be nonnegative int")
        if _nonnegative_int(row.get("triad_count")) is None:
            errors.append(f"triad_incidence_rows[{index}].triad_count: must be nonnegative int")
        for key in (
            "exact_lock_residual_rms",
            "exact_lock_residual_max",
            "carrier_shell_radius_mean",
            "triad_shell_spread_mean",
        ):
            value = _finite_float(row.get(key))
            if value is None:
                errors.append(f"triad_incidence_rows[{index}].{key}: must be finite")
            elif value < -1.0e-12:
                errors.append(f"triad_incidence_rows[{index}].{key}: must be nonnegative")
        for key in (
            "incidence_density",
            "cycle_basis_proxy",
            "exact_lock_near_lock_fraction",
            "exact_lock_score",
            "mode_concentration_fraction",
        ):
            _check_fraction(errors, f"triad_incidence_rows[{index}].{key}", row.get(key))
        if _nonnegative_int(row.get("cycle_rank_proxy")) is None:
            errors.append(f"triad_incidence_rows[{index}].cycle_rank_proxy: must be nonnegative int")
        if _nonnegative_int(row.get("mode_graph_edge_count")) is None:
            errors.append(f"triad_incidence_rows[{index}].mode_graph_edge_count: must be nonnegative int")
        if _nonnegative_int(row.get("mode_graph_component_count")) is None:
            errors.append(f"triad_incidence_rows[{index}].mode_graph_component_count: must be nonnegative int")
        if row.get("dominant_mode_key") is not None and not isinstance(row.get("dominant_mode_key"), list):
            errors.append(f"triad_incidence_rows[{index}].dominant_mode_key: must be list or null")
        if row.get("selected_mode_keys") is not None and not isinstance(row.get("selected_mode_keys"), list):
            errors.append(f"triad_incidence_rows[{index}].selected_mode_keys: must be list or null")
        incidence_records = row.get("incidence_records")
        if not isinstance(incidence_records, list):
            errors.append(f"triad_incidence_rows[{index}].incidence_records: must be list")
        else:
            expected_count = _nonnegative_int(row.get("triad_count")) or 0
            if len(incidence_records) != expected_count:
                errors.append(
                    f"triad_incidence_rows[{index}].incidence_records: length must match triad_count"
                )
            for j, record in enumerate(incidence_records):
                if not isinstance(record, dict):
                    errors.append(f"triad_incidence_rows[{index}].incidence_records[{j}]: must be object")
                    continue
                _check_incidence_record(record, f"triad_incidence_rows[{index}].incidence_records[{j}]", errors)

    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
        aggregate = {}
    processed_frames = _nonnegative_int(aggregate.get("processed_frames"))
    if processed_frames is None:
        errors.append("aggregate.processed_frames: must be nonnegative int")
        processed_frames = 0
    if processed_frames != len(rows):
        errors.append("aggregate.processed_frames: must match row count")
    for key in ("ok_frames", "partial_frames", "error_frames"):
        if _nonnegative_int(aggregate.get(key)) is None:
            errors.append(f"aggregate.{key}: must be nonnegative int")
    if (
        _nonnegative_int(aggregate.get("ok_frames")) is not None
        and _nonnegative_int(aggregate.get("partial_frames")) is not None
        and _nonnegative_int(aggregate.get("error_frames")) is not None
    ):
        total = (
            int(aggregate.get("ok_frames", 0))
            + int(aggregate.get("partial_frames", 0))
            + int(aggregate.get("error_frames", 0))
        )
        if total != processed_frames:
            errors.append("aggregate row status counts must sum to processed_frames")
    if _nonnegative_int(aggregate.get("top_k")) is None:
        errors.append("aggregate.top_k: must be nonnegative int")
    for key in (
        "carrier_mode_count_mean",
        "triad_count_mean",
        "cycle_rank_proxy_mean",
        "exact_lock_residual_rms_mean",
    ):
        value = _finite_float(aggregate.get(key))
        if value is None:
            errors.append(f"aggregate.{key}: must be finite")
        elif value < -1.0e-12:
            errors.append(f"aggregate.{key}: must be nonnegative")
    for key in (
        "incidence_density_mean",
        "exact_lock_score_mean",
    ):
        _check_fraction(errors, f"aggregate.{key}", aggregate.get(key))
    for key in (
        "incidence_density_vs_cycle_rank_correlation",
        "exact_lock_score_vs_density_correlation",
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
        "scan_contract": payload.get("contract"),
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
