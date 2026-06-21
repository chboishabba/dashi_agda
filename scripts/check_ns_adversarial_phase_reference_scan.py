#!/usr/bin/env python3
"""Validate ns_adversarial_phase_reference_scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_adversarial_phase_reference_scan.py"
CONTRACT = "check_ns_adversarial_phase_reference_scan"
SOURCE_CONTRACT = "ns_adversarial_phase_reference_scan"
ROUTE_DECISION = "FAIL_CLOSED_NS_ADVERSARIAL_PHASE_REFERENCE_SCAN_CHECK"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_ADVERSARIAL_PHASE_REFERENCE_SCAN"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_adversarial_phase_reference_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_adversarial_phase_reference_scan_N128_20260621.json"
)

CONTROL_CARD = {
    "O": "Validate adversarial phase-reference telemetry output.",
    "R": "Check schema, authority flags, explicit non-promotion markers, row counts, and candidate-reference metrics.",
    "C": SCRIPT_NAME,
    "S": "Fail-closed checker for malformed phase-reference telemetry surfaces.",
    "L": "Load the scan JSON, validate rows and aggregates, then emit a checker receipt.",
    "P": ROUTE_DECISION,
    "G": "Checker remains empirical and non-promoting.",
    "F": "Any malformed field, authority drift, or promoted-like marker is a hard error.",
}

SOURCE_CONTROL_CARD = {
    "O": "Scan adversarial phase-reference candidates for the raw N128 triad proxy.",
    "R": (
        "Compare a small family of global and shell-affine phase references against the same selected "
        "modes, then report the reference that maximizes constructive triad score."
    ),
    "C": "scripts/ns_adversarial_phase_reference_scan.py",
    "S": "Telemetry only; the winning reference is empirical and not a theorem or route promotion.",
    "L": (
        "Load raw frames, build selected Fourier-vorticity modes, evaluate candidate phase references, "
        "and emit fail-closed per-frame and aggregate telemetry."
    ),
    "P": "FAIL_CLOSED_NS_ADVERSARIAL_PHASE_REFERENCE_SCAN",
    "G": "No theorem, Clay, or promotion claim is inferred from the reference winner.",
    "F": "A zero-phase baseline is not privileged; the geometry-dependent candidate family may choose another reference.",
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

EXPECTED_NON_PROMOTION_MARKERS = {
    "candidate_only": True,
    "empirical_non_promoting": True,
    "promotion_claim": False,
    "theorem_claim": False,
    "clay_claim": False,
    "route_promoted": False,
    "best_reference_promoted": False,
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


def _positive_int(value: Any) -> int | None:
    parsed = _nonnegative_int(value)
    if parsed is None or parsed <= 0:
        return None
    return parsed


def _fraction_ok(value: Any) -> bool:
    parsed = _finite_float(value)
    return parsed is not None and -1.0e-12 <= parsed <= 1.0 + 1.0e-12


def _validate_authority(payload: dict[str, Any], errors: list[str]) -> None:
    authority = payload.get("authority")
    if not isinstance(authority, dict):
        errors.append("authority: must be object")
        return
    for key, expected in EXPECTED_AUTHORITY.items():
        if authority.get(key) is not expected:
            errors.append(f"authority.{key}: must be {expected!r}")


def _validate_non_promotion_markers(payload: dict[str, Any], errors: list[str]) -> None:
    markers = payload.get("non_promotion_markers")
    if not isinstance(markers, dict):
        errors.append("non_promotion_markers: must be object")
        return
    for key, expected in EXPECTED_NON_PROMOTION_MARKERS.items():
        if markers.get(key) is not expected:
            errors.append(f"non_promotion_markers.{key}: must be {expected!r}")


def _validate_candidate_row(
    row: dict[str, Any],
    index: int,
    errors: list[str],
) -> tuple[bool, bool]:
    if row.get("non_promoting") is not True:
        errors.append(f"phase_reference_rows[{index}].non_promoting: must be true")
    for key in ("promotion_claim", "theorem_claim", "clay_claim"):
        if row.get(key) is not False:
            errors.append(f"phase_reference_rows[{index}].{key}: must be false")

    is_ok = row.get("status") == OK_STATUS
    is_partial = row.get("status") == PARTIAL_STATUS
    if row.get("status") not in ALLOWED_STATUSES:
        errors.append(f"phase_reference_rows[{index}].status: must be ok|partial|error")
        is_ok = False
        is_partial = False

    if _nonnegative_int(row.get("frame")) is None:
        errors.append(f"phase_reference_rows[{index}].frame: must be nonnegative int")
    if _nonnegative_int(row.get("snapshot_index")) is None:
        errors.append(f"phase_reference_rows[{index}].snapshot_index: must be nonnegative int")
    if _finite_float(row.get("orbit_phase")) is None:
        errors.append(f"phase_reference_rows[{index}].orbit_phase: must be finite")
    if row.get("reference_family") != "global_constant_plus_shell_affine":
        errors.append(f"phase_reference_rows[{index}].reference_family: unexpected value")

    if is_partial:
        if _nonnegative_int(row.get("triad_count")) != 0:
            errors.append(f"phase_reference_rows[{index}].triad_count: must be 0 for partial rows")
        if _nonnegative_int(row.get("reference_candidate_count")) != 0:
            errors.append(f"phase_reference_rows[{index}].reference_candidate_count: must be 0 for partial rows")
        if row.get("reference_candidates") not in ([], None):
            errors.append(f"phase_reference_rows[{index}].reference_candidates: must be empty for partial rows")
        if row.get("best_reference_id") is not None:
            errors.append(f"phase_reference_rows[{index}].best_reference_id: must be null for partial rows")
        return is_ok, is_partial

    if not isinstance(row.get("reference_candidates"), list) or not row["reference_candidates"]:
        errors.append(f"phase_reference_rows[{index}].reference_candidates: must be non-empty list")
        return is_ok, is_partial

    candidate_count = _nonnegative_int(row.get("reference_candidate_count"))
    if candidate_count is None:
        errors.append(f"phase_reference_rows[{index}].reference_candidate_count: must be nonnegative int")
    elif candidate_count != len(row["reference_candidates"]):
        errors.append(f"phase_reference_rows[{index}].reference_candidate_count: length mismatch")

    candidate_ids: set[str] = set()
    candidate_by_id: dict[str, dict[str, Any]] = {}
    candidate_ranks: list[int] = []
    for c_index, candidate in enumerate(row["reference_candidates"]):
        if not isinstance(candidate, dict):
            errors.append(f"phase_reference_rows[{index}].reference_candidates[{c_index}]: must be object")
            continue
        ref_id = candidate.get("reference_id")
        if not isinstance(ref_id, str) or not ref_id:
            errors.append(f"phase_reference_rows[{index}].reference_candidates[{c_index}].reference_id: must be non-empty string")
        else:
            candidate_ids.add(ref_id)
            candidate_by_id[ref_id] = candidate
        if candidate.get("reference_kind") not in {"global", "structured"}:
            errors.append(f"phase_reference_rows[{index}].reference_candidates[{c_index}].reference_kind: must be global|structured")
        if _finite_float(candidate.get("phase_slope")) is None:
            errors.append(f"phase_reference_rows[{index}].reference_candidates[{c_index}].phase_slope: must be finite")
        if _finite_float(candidate.get("phase_offset")) is None:
            errors.append(f"phase_reference_rows[{index}].reference_candidates[{c_index}].phase_offset: must be finite")
        if _finite_float(candidate.get("phase_shift_rms")) is None or float(candidate.get("phase_shift_rms")) < 0.0:
            errors.append(f"phase_reference_rows[{index}].reference_candidates[{c_index}].phase_shift_rms: must be finite nonnegative")
        for key in (
            "constructive_weight_fraction",
            "orbit_coherence",
            "phase_alignment_fraction",
        ):
            if not _fraction_ok(candidate.get(key)):
                errors.append(f"phase_reference_rows[{index}].reference_candidates[{c_index}].{key}: must be finite fraction in [0,1]")
        for key in ("phase_bias", "orbit_phase_strength"):
            if _finite_float(candidate.get(key)) is None:
                errors.append(f"phase_reference_rows[{index}].reference_candidates[{c_index}].{key}: must be finite")
        if _positive_int(candidate.get("triad_count")) is None:
            errors.append(f"phase_reference_rows[{index}].reference_candidates[{c_index}].triad_count: must be positive int")
        rank_value = _positive_int(candidate.get("reference_rank"))
        if rank_value is None:
            errors.append(f"phase_reference_rows[{index}].reference_candidates[{c_index}].reference_rank: must be positive int")
        else:
            candidate_ranks.append(rank_value)

    if candidate_ranks and sorted(candidate_ranks) != list(range(1, len(candidate_ranks) + 1)):
        errors.append(f"phase_reference_rows[{index}].reference_candidates: ranks must form 1..N")

    best_reference_id = row.get("best_reference_id")
    if not isinstance(best_reference_id, str) or not best_reference_id:
        errors.append(f"phase_reference_rows[{index}].best_reference_id: must be non-empty string")
    elif best_reference_id not in candidate_ids:
        errors.append(f"phase_reference_rows[{index}].best_reference_id: must appear in reference_candidates")
    else:
        best_candidate = candidate_by_id[best_reference_id]
        first_candidate = row["reference_candidates"][0]
        if not isinstance(first_candidate, dict) or first_candidate.get("reference_id") != best_reference_id:
            errors.append(f"phase_reference_rows[{index}].reference_candidates[0]: must be the winning candidate")
        if _positive_int(best_candidate.get("reference_rank")) != 1:
            errors.append(f"phase_reference_rows[{index}].best_reference_rank: winner must have rank 1")
        if row.get("best_reference_kind") != best_candidate.get("reference_kind"):
            errors.append(f"phase_reference_rows[{index}].best_reference_kind: mismatch with winning candidate")
        if _positive_int(row.get("best_reference_rank")) != _positive_int(best_candidate.get("reference_rank")):
            errors.append(f"phase_reference_rows[{index}].best_reference_rank: mismatch with winning candidate")
        if _finite_float(row.get("best_reference_phase_slope")) != _finite_float(best_candidate.get("phase_slope")):
            errors.append(f"phase_reference_rows[{index}].best_reference_phase_slope: mismatch with winning candidate")
        if _finite_float(row.get("best_reference_phase_offset")) != _finite_float(best_candidate.get("phase_offset")):
            errors.append(f"phase_reference_rows[{index}].best_reference_phase_offset: mismatch with winning candidate")
        if _finite_float(row.get("best_reference_phase_shift_rms")) != _finite_float(best_candidate.get("phase_shift_rms")):
            errors.append(f"phase_reference_rows[{index}].best_reference_phase_shift_rms: mismatch with winning candidate")
        if _finite_float(row.get("best_constructive_weight_fraction")) != _finite_float(best_candidate.get("constructive_weight_fraction")):
            errors.append(f"phase_reference_rows[{index}].best_constructive_weight_fraction: mismatch with winning candidate")
        for key in ("best_global_reference_id", "best_structured_reference_id"):
            if not isinstance(row.get(key), str) or not row.get(key):
                errors.append(f"phase_reference_rows[{index}].{key}: must be non-empty string")

    for key in (
        "best_reference_kind",
    ):
        value = row.get(key)
        if value is not None and (not isinstance(value, str) or not value):
            errors.append(f"phase_reference_rows[{index}].{key}: must be null or non-empty string")

    for key in ("selected_mode_count", "triad_count", "reference_candidate_count"):
        if _positive_int(row.get(key)) is None:
            errors.append(f"phase_reference_rows[{index}].{key}: must be positive int")
    for key in ("best_reference_rank", "best_global_reference_rank", "best_structured_reference_rank", "zero_reference_rank"):
        if _positive_int(row.get(key)) is None:
            errors.append(f"phase_reference_rows[{index}].{key}: must be positive int")

    for key in (
        "mode_concentration_fraction",
        "zero_reference_constructive_weight_fraction",
        "best_constructive_weight_fraction",
        "best_orbit_coherence",
        "best_phase_alignment_fraction",
        "best_reference_phase_shift_rms",
        "best_reference_phase_offset",
        "best_reference_phase_slope",
        "best_orbit_phase_strength",
        "best_global_constructive_weight_fraction",
        "best_structured_constructive_weight_fraction",
        "best_minus_zero_constructive_gap",
        "best_minus_best_global_gap",
        "best_structured_minus_best_global_gap",
        "shell_radius_mean",
        "triad_shell_spread_mean",
    ):
        if _finite_float(row.get(key)) is None:
            errors.append(f"phase_reference_rows[{index}].{key}: must be finite")

    if row.get("winner_is_zero_reference") not in {True, False}:
        errors.append(f"phase_reference_rows[{index}].winner_is_zero_reference: must be bool")
    if row.get("winner_is_structured_reference") not in {True, False}:
        errors.append(f"phase_reference_rows[{index}].winner_is_structured_reference: must be bool")
    if row.get("reference_geometry_gap_visible") not in {True, False}:
        errors.append(f"phase_reference_rows[{index}].reference_geometry_gap_visible: must be bool")

    return is_ok, is_partial


def _validate_rows(payload: dict[str, Any], errors: list[str]) -> tuple[list[dict[str, Any]], int, int, int]:
    rows = payload.get("phase_reference_rows")
    if not isinstance(rows, list) or not rows:
        errors.append("phase_reference_rows: must be non-empty list")
        return [], 0, 0, 0

    ok_rows = 0
    partial_rows = 0
    error_rows = 0
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            errors.append(f"phase_reference_rows[{index}]: must be object")
            error_rows += 1
            continue
        before = len(errors)
        is_ok, is_partial = _validate_candidate_row(row, index, errors)
        row_had_errors = len(errors) > before
        if row.get("status") == ERROR_STATUS or row_had_errors or not (is_ok or is_partial):
            error_rows += 1
        elif is_ok:
            ok_rows += 1
        elif is_partial:
            partial_rows += 1
    return rows, ok_rows, partial_rows, error_rows


def _validate_aggregate(payload: dict[str, Any], row_count: int, ok_rows: int, partial_rows: int, error_rows: int, errors: list[str]) -> None:
    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
        return

    processed_frames = _nonnegative_int(aggregate.get("processed_frames"))
    if processed_frames is None:
        errors.append("aggregate.processed_frames: must be nonnegative int")
    elif processed_frames != row_count:
        errors.append("aggregate.processed_frames: row-count mismatch")

    if _nonnegative_int(aggregate.get("ok_frames")) != ok_rows:
        errors.append("aggregate.ok_frames mismatch")
    if _nonnegative_int(aggregate.get("partial_frames")) != partial_rows:
        errors.append("aggregate.partial_frames mismatch")
    if _nonnegative_int(aggregate.get("error_frames")) != error_rows:
        errors.append("aggregate.error_frames mismatch")

    if aggregate.get("reference_family") != "global_constant_plus_shell_affine":
        errors.append("aggregate.reference_family: unexpected value")

    if ok_rows > 0:
        for key in ("top_k", "pool_multiplier", "reference_candidate_count"):
            if _positive_int(aggregate.get(key)) is None:
                errors.append(f"aggregate.{key}: must be positive int")
    else:
        for key in ("top_k", "pool_multiplier", "reference_candidate_count"):
            if aggregate.get(key) is not None:
                errors.append(f"aggregate.{key}: must be null when there are no ok rows")

    for key in (
        "best_reference_is_zero_fraction",
        "best_reference_is_structured_fraction",
    ):
        value = aggregate.get(key)
        if value is not None and not _fraction_ok(value):
            errors.append(f"aggregate.{key}: must be finite fraction in [0,1] or null")

    for key in (
        "zero_reference_rank_mean",
        "zero_reference_constructive_weight_fraction_mean",
        "best_constructive_weight_fraction_mean",
        "best_global_constructive_weight_fraction_mean",
        "best_structured_constructive_weight_fraction_mean",
        "best_minus_zero_constructive_gap_mean",
        "best_minus_best_global_gap_mean",
        "best_structured_minus_best_global_gap_mean",
        "mode_concentration_fraction_mean",
        "triad_shell_spread_mean",
    ):
        value = aggregate.get(key)
        if value is not None and _finite_float(value) is None:
            errors.append(f"aggregate.{key}: must be finite or null")

    if aggregate.get("gap_vs_shell_spread_correlation") is not None:
        parsed = _finite_float(aggregate.get("gap_vs_shell_spread_correlation"))
        if parsed is None or parsed < -1.0 - 1.0e-12 or parsed > 1.0 + 1.0e-12:
            errors.append("aggregate.gap_vs_shell_spread_correlation: must be finite in [-1,1] or null")

    if aggregate.get("winner_zero_rank_fraction") is not None and not _fraction_ok(aggregate.get("winner_zero_rank_fraction")):
        errors.append("aggregate.winner_zero_rank_fraction: must be finite fraction in [0,1] or null")


def main() -> int:
    args = _parse_args()
    path = _input_path(args)
    errors: list[str] = []
    warnings: list[str] = []
    try:
        payload = _load_json(path)
    except Exception as exc:  # noqa: BLE001
        result = {
            **CONTROL_CARD,
            "contract": CONTRACT,
            "route_decision": ROUTE_DECISION,
            "schema_version": SCHEMA_VERSION,
            "status": ERROR_STATUS,
            "ok": False,
            "errors": [str(exc)],
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(_json_text(result, args.pretty) + "\n", encoding="utf-8")
        print(_json_text(result, args.pretty))
        return 1

    if payload.get("contract") != SOURCE_CONTRACT:
        errors.append(f"contract: must be {SOURCE_CONTRACT!r}")
    if payload.get("schema_version") != SCHEMA_VERSION:
        errors.append(f"schema_version: must be {SCHEMA_VERSION!r}")
    if payload.get("status") not in ALLOWED_STATUSES:
        errors.append("status: must be ok|partial|error")
    if not isinstance(payload.get("inputs"), dict):
        errors.append("inputs: must be object")
    if not isinstance(payload.get("parameters"), dict):
        errors.append("parameters: must be object")
    if not isinstance(payload.get("warnings"), list):
        errors.append("warnings: must be list")
    if not isinstance(payload.get("errors"), list):
        errors.append("errors: must be list")

    _validate_authority(payload, errors)
    _validate_non_promotion_markers(payload, errors)
    inputs = payload.get("inputs") if isinstance(payload.get("inputs"), dict) else {}
    if not isinstance(inputs.get("raw_archive"), str) or not inputs.get("raw_archive"):
        errors.append("inputs.raw_archive: must be non-empty string")
    if not isinstance(inputs.get("output_json"), str) or not inputs.get("output_json"):
        errors.append("inputs.output_json: must be non-empty string")
    parameters = payload.get("parameters") if isinstance(payload.get("parameters"), dict) else {}
    if _positive_int(parameters.get("top_k")) is None:
        errors.append("parameters.top_k: must be positive int")
    if _positive_int(parameters.get("pool_multiplier")) is None:
        errors.append("parameters.pool_multiplier: must be positive int")
    zero_eps = _finite_float(parameters.get("zero_eps"))
    if zero_eps is None or zero_eps <= 0.0:
        errors.append("parameters.zero_eps: must be finite positive")
    for key in ("frame", "frame_limit"):
        value = parameters.get(key)
        if value is not None and _nonnegative_int(value) is None:
            errors.append(f"parameters.{key}: must be null or nonnegative int")
    structured_slopes = parameters.get("structured_slopes")
    if not isinstance(structured_slopes, list) or not structured_slopes:
        errors.append("parameters.structured_slopes: must be non-empty list")
    else:
        for index, slope in enumerate(structured_slopes):
            if _finite_float(slope) is None:
                errors.append(f"parameters.structured_slopes[{index}]: must be finite")
    rows, ok_rows, partial_rows, error_rows = _validate_rows(payload, errors)
    _validate_aggregate(payload, len(rows), ok_rows, partial_rows, error_rows, errors)

    if payload.get("route_decision") != SOURCE_ROUTE_DECISION:
        errors.append(f"route_decision: must be {SOURCE_ROUTE_DECISION!r}")
    if payload.get("script") != SOURCE_CONTROL_CARD["C"]:
        errors.append(f"script: must be {SOURCE_CONTROL_CARD['C']!r}")
    if payload.get("control_card") != SOURCE_CONTROL_CARD:
        errors.append("control_card: must match canonical scan control card")

    receipt = {
        **CONTROL_CARD,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
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
