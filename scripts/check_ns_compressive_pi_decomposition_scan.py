#!/usr/bin/env python3
"""Validate ns_compressive_pi_decomposition_scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_compressive_pi_decomposition_scan.py"
CONTRACT = "check_ns_compressive_pi_decomposition_scan"
SCAN_CONTRACT = "ns_compressive_pi_decomposition_scan"
SCAN_ROUTE_DECISION = "FAIL_CLOSED_NS_COMPRESSIVE_PI_DECOMPOSITION_SCAN"
CHECK_ROUTE_DECISION = "FAIL_CLOSED_NS_COMPRESSIVE_PI_DECOMPOSITION_SCAN_CHECK"

DEFAULT_SCAN_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_compressive_pi_decomposition_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "check_ns_compressive_pi_decomposition_scan_N128_20260621.json"
)

CONTROL_CARD = {
    "O": "Validate Pi decomposition scan output for schema and arithmetic invariants.",
    "R": (
        "Validate per-frame aggregate shape, sign-count accounting, compressive-vs-extensional "
        "dominance, and aggregate consistency for lambda_i*omega_i^2 telemetry."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed checker: schema failures, count mismatches, or invariant drift produce hard errors.",
    "L": "Load scan JSON, validate rows and aggregates, and emit checker status.",
    "P": CHECK_ROUTE_DECISION,
    "G": "Checker is empirical only.",
    "F": "All output invariants and schema fields are required for non-error rows.",
}

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
MISSING_REQUIRED_STATUS = "missing_required_field"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, MISSING_REQUIRED_STATUS, ERROR_STATUS}
TOLERANCE = 1.0e-12
CHECK_CARD_KEYS = ("O", "R", "C", "S", "L", "P", "G", "F")

FRAME_COUNT_KEYS = (
    "cell_count",
    "finite_cell_count",
    "lambda1_positive_count",
    "lambda1_negative_count",
    "lambda1_zero_count",
    "lambda2_positive_count",
    "lambda2_negative_count",
    "lambda2_zero_count",
    "lambda3_positive_count",
    "lambda3_negative_count",
    "lambda3_zero_count",
    "compressive_zone_cell_count",
    "compressive_zone_omega_nonzero_count",
    "compressive_dominates_count",
    "extensional_dominates_count",
    "dominance_tie_count",
    "pi1_positive_count",
    "pi1_negative_count",
    "pi1_zero_count",
    "pi2_positive_count",
    "pi2_negative_count",
    "pi2_zero_count",
    "pi3_positive_count",
    "pi3_negative_count",
    "pi3_zero_count",
)

FRAME_FRACTION_KEYS = (
    ("lambda1_positive_fraction", "lambda1_positive_count", "finite_cell_count"),
    ("lambda1_negative_fraction", "lambda1_negative_count", "finite_cell_count"),
    ("lambda1_zero_fraction", "lambda1_zero_count", "finite_cell_count"),
    ("lambda2_positive_fraction", "lambda2_positive_count", "finite_cell_count"),
    ("lambda2_negative_fraction", "lambda2_negative_count", "finite_cell_count"),
    ("lambda2_zero_fraction", "lambda2_zero_count", "finite_cell_count"),
    ("lambda3_positive_fraction", "lambda3_positive_count", "finite_cell_count"),
    ("lambda3_negative_fraction", "lambda3_negative_count", "finite_cell_count"),
    ("lambda3_zero_fraction", "lambda3_zero_count", "finite_cell_count"),
    ("pi1_positive_fraction", "pi1_positive_count", "compressive_zone_cell_count"),
    ("pi1_negative_fraction", "pi1_negative_count", "compressive_zone_cell_count"),
    ("pi1_zero_fraction", "pi1_zero_count", "compressive_zone_cell_count"),
    ("pi2_positive_fraction", "pi2_positive_count", "compressive_zone_cell_count"),
    ("pi2_negative_fraction", "pi2_negative_count", "compressive_zone_cell_count"),
    ("pi2_zero_fraction", "pi2_zero_count", "compressive_zone_cell_count"),
    ("pi3_positive_fraction", "pi3_positive_count", "compressive_zone_cell_count"),
    ("pi3_negative_fraction", "pi3_negative_count", "compressive_zone_cell_count"),
    ("pi3_zero_fraction", "pi3_zero_count", "compressive_zone_cell_count"),
    ("compressive_zone_omega_nonzero_fraction", "compressive_zone_omega_nonzero_count", "compressive_zone_cell_count"),
    ("compressive_dominates_fraction", "compressive_dominates_count", "compressive_zone_cell_count"),
    ("extensional_dominates_fraction", "extensional_dominates_count", "compressive_zone_cell_count"),
    ("dominance_tie_fraction", "dominance_tie_count", "compressive_zone_cell_count"),
)

AGGREGATE_COUNT_KEYS = (
    ("global_lambda1_positive_count", "lambda1_positive_count"),
    ("global_lambda1_negative_count", "lambda1_negative_count"),
    ("global_lambda1_zero_count", "lambda1_zero_count"),
    ("global_lambda2_positive_count", "lambda2_positive_count"),
    ("global_lambda2_negative_count", "lambda2_negative_count"),
    ("global_lambda2_zero_count", "lambda2_zero_count"),
    ("global_lambda3_positive_count", "lambda3_positive_count"),
    ("global_lambda3_negative_count", "lambda3_negative_count"),
    ("global_lambda3_zero_count", "lambda3_zero_count"),
    ("global_compressive_zone_cell_count", "compressive_zone_cell_count"),
    ("global_compressive_zone_omega_nonzero_count", "compressive_zone_omega_nonzero_count"),
    ("global_compressive_dominates_count", "compressive_dominates_count"),
    ("global_extensional_dominates_count", "extensional_dominates_count"),
    ("global_dominance_tie_count", "dominance_tie_count"),
    ("global_pi1_positive_count", "pi1_positive_count"),
    ("global_pi1_negative_count", "pi1_negative_count"),
    ("global_pi1_zero_count", "pi1_zero_count"),
    ("global_pi2_positive_count", "pi2_positive_count"),
    ("global_pi2_negative_count", "pi2_negative_count"),
    ("global_pi2_zero_count", "pi2_zero_count"),
    ("global_pi3_positive_count", "pi3_positive_count"),
    ("global_pi3_negative_count", "pi3_negative_count"),
    ("global_pi3_zero_count", "pi3_zero_count"),
)

AGGREGATE_FLOAT_KEYS = (
    "global_pi1_sum",
    "global_pi2_sum",
    "global_pi3_sum",
    "global_pi_sum",
    "global_pi_sum_abs",
    "global_pi1_abs_sum",
    "global_pi2_abs_sum",
    "global_pi3_abs_sum",
    "global_omega1_sq_sum",
    "global_omega2_sq_sum",
    "global_omega3_sq_sum",
)

AGGREGATE_FRACTION_KEYS = (
    ("global_lambda1_positive_fraction", "global_lambda1_positive_count", "global_finite_cell_count"),
    ("global_lambda1_negative_fraction", "global_lambda1_negative_count", "global_finite_cell_count"),
    ("global_lambda1_zero_fraction", "global_lambda1_zero_count", "global_finite_cell_count"),
    ("global_lambda2_positive_fraction", "global_lambda2_positive_count", "global_finite_cell_count"),
    ("global_lambda2_negative_fraction", "global_lambda2_negative_count", "global_finite_cell_count"),
    ("global_lambda2_zero_fraction", "global_lambda2_zero_count", "global_finite_cell_count"),
    ("global_lambda3_positive_fraction", "global_lambda3_positive_count", "global_finite_cell_count"),
    ("global_lambda3_negative_fraction", "global_lambda3_negative_count", "global_finite_cell_count"),
    ("global_lambda3_zero_fraction", "global_lambda3_zero_count", "global_finite_cell_count"),
    ("global_compressive_zone_omega_nonzero_fraction", "global_compressive_zone_omega_nonzero_count", "global_compressive_zone_cell_count"),
    ("global_compressive_dominates_fraction", "global_compressive_dominates_count", "global_compressive_zone_cell_count"),
    ("global_extensional_dominates_fraction", "global_extensional_dominates_count", "global_compressive_zone_cell_count"),
    ("global_dominance_tie_fraction", "global_dominance_tie_count", "global_compressive_zone_cell_count"),
    ("global_pi1_positive_fraction", "global_pi1_positive_count", "global_compressive_zone_cell_count"),
    ("global_pi1_negative_fraction", "global_pi1_negative_count", "global_compressive_zone_cell_count"),
    ("global_pi1_zero_fraction", "global_pi1_zero_count", "global_compressive_zone_cell_count"),
    ("global_pi2_positive_fraction", "global_pi2_positive_count", "global_compressive_zone_cell_count"),
    ("global_pi2_negative_fraction", "global_pi2_negative_count", "global_compressive_zone_cell_count"),
    ("global_pi2_zero_fraction", "global_pi2_zero_count", "global_compressive_zone_cell_count"),
    ("global_pi3_positive_fraction", "global_pi3_positive_count", "global_compressive_zone_cell_count"),
    ("global_pi3_negative_fraction", "global_pi3_negative_count", "global_compressive_zone_cell_count"),
    ("global_pi3_zero_fraction", "global_pi3_zero_count", "global_compressive_zone_cell_count"),
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--scan-json",
        type=Path,
        default=DEFAULT_SCAN_JSON,
        help="Path to ns_compressive_pi_decomposition_scan output.",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT_JSON,
        help="Path to checker output JSON.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print output.")
    return parser.parse_args()
    

def _parse_arguments() -> argparse.Namespace:
    return _parse_args()


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing scan json: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"scan json must be an object: {path}")
    return payload


def _write_json(path: Path, payload: dict[str, Any], pretty: bool) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if pretty:
        text = json.dumps(payload, sort_keys=True, indent=2, ensure_ascii=False, allow_nan=False) + "\n"
    else:
        text = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False) + "\n"
    path.write_text(text, encoding="utf-8")


def _join_path(parts: tuple[Any, ...]) -> str:
    if not parts:
        return ""
    pieces: list[str] = []
    for part in parts:
        if isinstance(part, int):
            if not pieces:
                pieces.append(f"[{part}]")
            else:
                pieces[-1] = f"{pieces[-1]}[{part}]"
            continue
        if pieces:
            pieces.append(f".{part}")
        else:
            pieces.append(str(part))
    return "".join(pieces)


def _record_error(errors: list[str], path: tuple[Any, ...], message: str) -> None:
    label = _join_path(path)
    errors.append(f"{label}: {message}" if label else message)


def _record_warning(warnings: list[str], path: tuple[Any, ...], message: str) -> None:
    label = _join_path(path)
    warnings.append(f"{label}: {message}" if label else message)


def _coerce_nonnegative_int(value: Any) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if isinstance(value, float) and math.isfinite(value) and value.is_integer():
        return int(value) if int(value) >= 0 else None
    return None


def _coerce_finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _coerce_nonnegative_float(value: Any) -> float | None:
    parsed = _coerce_finite_float(value)
    if parsed is None or parsed < 0.0:
        return None
    return parsed


def _coerce_nonempty_str(value: Any) -> str | None:
    if not isinstance(value, str):
        return None
    stripped = value.strip()
    return stripped if stripped else None


def _coerce_bool(value: Any) -> bool | None:
    return value if isinstance(value, bool) else None


def _expected_fraction(count: int | None, denominator: int | None) -> float:
    if count is None or denominator is None:
        return float("nan")
    if denominator <= 0:
        return 0.0
    return float(count) / float(denominator)


def _check_control_card(payload: dict[str, Any], errors: list[str]) -> None:
    for key in CHECK_CARD_KEYS:
        if _coerce_nonempty_str(payload.get(key)) is None:
            _record_error(errors, (key,), "must be a non-empty string")


def _check_contract(payload: dict[str, Any], errors: list[str]) -> None:
    if payload.get("contract") != SCAN_CONTRACT:
        _record_error(errors, ("contract",), f"must be {SCAN_CONTRACT!r}")


def _check_route(payload: dict[str, Any], errors: list[str]) -> None:
    if payload.get("route_decision") != SCAN_ROUTE_DECISION:
        _record_error(errors, ("route_decision",), f"must be {SCAN_ROUTE_DECISION!r}")


def _check_status(payload: dict[str, Any], errors: list[str]) -> None:
    if payload.get("status") not in ALLOWED_STATUSES:
        _record_error(errors, ("status",), f"must be one of {sorted(ALLOWED_STATUSES)!r}")


def _check_authority(payload: dict[str, Any], errors: list[str]) -> None:
    authority = payload.get("authority")
    if not isinstance(authority, dict):
        _record_error(errors, ("authority",), "must be an object")
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
        actual = _coerce_bool(authority.get(key))
        if actual is None:
            _record_error(errors, ("authority", key), "must be bool")
            continue
        if actual is not expected_value:
            _record_error(errors, ("authority", key), f"must be {expected_value!r}")


def _check_inputs(payload: dict[str, Any], warnings: list[str], errors: list[str]) -> None:
    inputs = payload.get("inputs")
    if not isinstance(inputs, dict):
        inputs = payload.get("input")
    if not isinstance(inputs, dict):
        _record_error(errors, ("inputs",), "must be an object")
        return

    if _coerce_nonempty_str(inputs.get("raw_archive")) is None:
        _record_error(errors, ("inputs", "raw_archive"), "must be non-empty string")
    if inputs.get("frame") is not None and _coerce_nonnegative_int(inputs.get("frame")) is None:
        _record_error(errors, ("inputs", "frame"), "must be null or nonnegative int")
    if inputs.get("frame_limit") is not None and _coerce_nonnegative_int(inputs.get("frame_limit")) is None:
        _record_error(errors, ("inputs", "frame_limit"), "must be null or nonnegative int")
    if _coerce_nonnegative_float(inputs.get("zero_eps")) is None:
        _record_error(errors, ("inputs", "zero_eps"), "must be finite nonnegative")
    if _coerce_nonnegative_int(inputs.get("raw_bundle_frame_count")) is None and inputs.get("raw_bundle_frame_count") is not None:
        _record_warning(warnings, ("inputs", "raw_bundle_frame_count"), "must be nonnegative int if present")

    selected_frames = inputs.get("selected_frames")
    if selected_frames is None:
        return
    if not isinstance(selected_frames, list):
        _record_error(errors, ("inputs", "selected_frames"), "must be list if present")
        return
    for index, value in enumerate(selected_frames):
        if _coerce_nonnegative_int(value) is None:
            _record_error(errors, ("inputs", "selected_frames", index), "each selected frame must be nonnegative int")


def _validate_fraction(
    path: tuple[Any, ...],
    numerator_key: str,
    denominator_key: str,
    row: dict[str, Any],
    warnings: list[str],
    errors: list[str],
) -> None:
    count = _coerce_nonnegative_int(row.get(numerator_key))
    denom = _coerce_nonnegative_int(row.get(denominator_key))
    fraction = _coerce_finite_float(row.get(path[-1] if isinstance(path[-1], str) else ""))
    if fraction is None:
        _record_error(errors, path, "must be finite")
        return
    if fraction < 0.0 or fraction > 1.0:
        _record_warning(warnings, path, "outside [0,1]")
    expected = _expected_fraction(count, denom)
    if math.isnan(expected):
        return
    if abs(fraction - expected) > TOLERANCE:
        _record_error(errors, path, f"expected {expected!r}, got {fraction!r}")


def _validate_sign_partition(
    row: dict[str, Any],
    prefix: str,
    zone_key: str,
    row_index: int,
    warnings: list[str],
    errors: list[str],
) -> None:
    pos = _coerce_nonnegative_int(row.get(f"{prefix}_positive_count"))
    neg = _coerce_nonnegative_int(row.get(f"{prefix}_negative_count"))
    zero = _coerce_nonnegative_int(row.get(f"{prefix}_zero_count"))
    zone = _coerce_nonnegative_int(row.get(zone_key))

    if pos is None:
        _record_error(errors, ("frames", row_index, f"{prefix}_positive_count"), "must be nonnegative int")
    if neg is None:
        _record_error(errors, ("frames", row_index, f"{prefix}_negative_count"), "must be nonnegative int")
    if zero is None:
        _record_error(errors, ("frames", row_index, f"{prefix}_zero_count"), "must be nonnegative int")
    if pos is not None and neg is not None and zero is not None and zone is not None and pos + neg + zero != zone:
        _record_error(
            errors,
            ("frames", row_index),
            f"{prefix} sign partition mismatch with {zone_key}: expected {zone}, got {pos + neg + zero}",
        )

    for fraction_key, count_key, _ in FRAME_FRACTION_KEYS:
        if not fraction_key.startswith(f"{prefix}_"):
            continue
        count = _coerce_nonnegative_int(row.get(count_key))
        fraction = _coerce_finite_float(row.get(fraction_key))
        if fraction is None:
            _record_error(errors, ("frames", row_index, fraction_key), "must be finite")
            continue
        if fraction < 0.0 or fraction > 1.0:
            _record_warning(warnings, ("frames", row_index, fraction_key), "outside [0,1]")

    if zone is None or pos is None or neg is None or zero is None:
        return

    for fraction_key, count_key, denom_key in FRAME_FRACTION_KEYS:
        if not fraction_key.startswith(f"{prefix}_"):
            continue
        denom = _coerce_nonnegative_int(row.get(denom_key))
        count = _coerce_nonnegative_int(row.get(count_key))
        fraction = _coerce_finite_float(row.get(fraction_key))
        if count is None or denom is None or fraction is None:
            continue
        expected = _expected_fraction(count, denom)
        if math.isnan(expected):
            continue
        if abs(fraction - expected) > TOLERANCE:
            _record_error(
                errors,
                ("frames", row_index, fraction_key),
                f"expected {expected!r}, got {fraction!r}",
            )


def _validate_dominance(row: dict[str, Any], row_index: int, warnings: list[str], errors: list[str]) -> None:
    zone = _coerce_nonnegative_int(row.get("compressive_zone_cell_count"))
    comp_d = _coerce_nonnegative_int(row.get("compressive_dominates_count"))
    ext_d = _coerce_nonnegative_int(row.get("extensional_dominates_count"))
    tie = _coerce_nonnegative_int(row.get("dominance_tie_count"))

    if zone is None:
        return
    if comp_d is not None and ext_d is not None and tie is not None and (comp_d + ext_d + tie != zone):
        _record_error(
            errors,
            ("frames", row_index),
            "dominance counts must partition compressive_zone_cell_count",
        )

    for key in ("compressive_dominates_fraction", "extensional_dominates_fraction", "dominance_tie_fraction"):
        fraction = _coerce_finite_float(row.get(key))
        count = _coerce_nonnegative_int(row.get(key.replace("_fraction", "_count")))
        if fraction is None:
            _record_error(errors, ("frames", row_index, key), "must be finite")
            continue
        if fraction < 0.0 or fraction > 1.0:
            _record_warning(warnings, ("frames", row_index, key), "outside [0,1]")
        expected = _expected_fraction(count, zone)
        if math.isnan(expected):
            continue
        if abs(fraction - expected) > TOLERANCE:
            _record_error(errors, ("frames", row_index, key), f"expected {expected!r}, got {fraction!r}")

    gap_sum = _coerce_finite_float(row.get("dominance_gap_sum"))
    gap_min = _coerce_finite_float(row.get("dominance_gap_min"))
    gap_max = _coerce_finite_float(row.get("dominance_gap_max"))
    if gap_sum is None and zone != 0:
        _record_error(errors, ("frames", row_index, "dominance_gap_sum"), "must be finite")
    if gap_min is not None and gap_max is not None and gap_min > gap_max:
        _record_error(errors, ("frames", row_index), "dominance_gap_min > dominance_gap_max")


def _validate_frame_row(row: dict[str, Any], index: int, warnings: list[str], errors: list[str]) -> None:
    status = row.get("status")
    if status not in ALLOWED_STATUSES:
        _record_error(errors, ("frames", index, "status"), "must be one of ok|partial|missing_required_field|error")
        status = ERROR_STATUS

    if _coerce_nonnegative_int(row.get("frame")) is None:
        _record_error(errors, ("frames", index, "frame"), "must be nonnegative int")
    if _coerce_nonnegative_int(row.get("snapshot_index")) is None:
        _record_error(errors, ("frames", index, "snapshot_index"), "must be nonnegative int")
    for key in ("source", "lambda2_source", "vorticity_source", "eigenframe_source"):
        if _coerce_nonempty_str(row.get(key)) is None:
            _record_error(errors, ("frames", index, key), "must be non-empty string")

    if status == ERROR_STATUS:
        row_errors = row.get("errors")
        if not isinstance(row_errors, list) or not row_errors:
            _record_error(errors, ("frames", index, "errors"), "error rows must include non-empty errors list")
        return

    for key in FRAME_COUNT_KEYS:
        if _coerce_nonnegative_int(row.get(key)) is None:
            _record_error(errors, ("frames", index, key), "must be nonnegative int")

    frame_count = _coerce_nonnegative_int(row.get("cell_count"))
    finite_count = _coerce_nonnegative_int(row.get("finite_cell_count"))
    if frame_count is not None and finite_count is not None and finite_count > frame_count:
        _record_error(errors, ("frames", index), "finite_cell_count cannot exceed cell_count")

    if finite_count is not None:
        _validate_sign_partition(row, "lambda1", "finite_cell_count", index, warnings, errors)
        _validate_sign_partition(row, "lambda2", "finite_cell_count", index, warnings, errors)
        _validate_sign_partition(row, "lambda3", "finite_cell_count", index, warnings, errors)

    comp_count = _coerce_nonnegative_int(row.get("compressive_zone_cell_count"))
    if finite_count is not None and comp_count is not None and comp_count > finite_count:
        _record_error(errors, ("frames", index, "compressive_zone_cell_count"), "cannot exceed finite_cell_count")
    omega_nonzero = _coerce_nonnegative_int(row.get("compressive_zone_omega_nonzero_count"))
    if comp_count is not None and omega_nonzero is not None and omega_nonzero > comp_count:
        _record_error(errors, ("frames", index, "compressive_zone_omega_nonzero_count"), "cannot exceed compressive_zone_cell_count")

    if comp_count is not None:
        _validate_sign_partition(row, "pi1", "compressive_zone_cell_count", index, warnings, errors)
        _validate_sign_partition(row, "pi2", "compressive_zone_cell_count", index, warnings, errors)
        _validate_sign_partition(row, "pi3", "compressive_zone_cell_count", index, warnings, errors)
        _validate_dominance(row, index, warnings, errors)

    for fraction_key, _, _ in FRAME_FRACTION_KEYS:
        if _coerce_finite_float(row.get(fraction_key)) is None:
            _record_error(errors, ("frames", index, fraction_key), "must be finite")

    pi_sum = _coerce_finite_float(row.get("pi_sum"))
    pi1_sum = _coerce_finite_float(row.get("pi1_sum"))
    pi2_sum = _coerce_finite_float(row.get("pi2_sum"))
    pi3_sum = _coerce_finite_float(row.get("pi3_sum"))
    if pi_sum is not None and pi1_sum is not None and pi2_sum is not None and pi3_sum is not None:
        expected = pi1_sum + pi2_sum + pi3_sum
        if abs(pi_sum - expected) > TOLERANCE:
            _record_error(errors, ("frames", index, "pi_sum"), f"expected {expected!r}, got {pi_sum!r}")

    for fraction_key, count_key, denom_key in FRAME_FRACTION_KEYS:
        fraction = _coerce_finite_float(row.get(fraction_key))
        if fraction is None:
            continue
        if fraction < 0.0 or fraction > 1.0:
            _record_warning(warnings, ("frames", index, fraction_key), "outside [0,1]")
        count = _coerce_nonnegative_int(row.get(count_key))
        denom = _coerce_nonnegative_int(row.get(denom_key))
        expected = _expected_fraction(count, denom)
        if math.isnan(expected):
            continue
        if abs(fraction - expected) > TOLERANCE:
            _record_error(errors, ("frames", index, fraction_key), f"expected {expected!r}, got {fraction!r}")


def _validate_frames(payload: dict[str, Any], warnings: list[str], errors: list[str]) -> tuple[int, dict[str, int]]:
    rows = payload.get("frames")
    if not isinstance(rows, list):
        _record_error(errors, ("frames",), "must be a list")
        return 0, {"ok_frames": 0, "partial_frames": 0, "missing_frames": 0, "error_frames": 0}

    status_counts = {"ok_frames": 0, "partial_frames": 0, "missing_frames": 0, "error_frames": 0}
    ok_rows = 0
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            _record_error(errors, ("frames", index), "must be an object")
            status_counts["error_frames"] += 1
            continue
        status = row.get("status")
        if status == OK_STATUS:
            status_counts["ok_frames"] += 1
            ok_rows += 1
        elif status == PARTIAL_STATUS:
            status_counts["partial_frames"] += 1
        elif status == MISSING_REQUIRED_STATUS:
            status_counts["missing_frames"] += 1
        elif status == ERROR_STATUS:
            status_counts["error_frames"] += 1
        else:
            status_counts["error_frames"] += 1
        _validate_frame_row(row, index, warnings, errors)
    return ok_rows, status_counts


def _validate_floats(expected: float, observed: float | None, path: tuple[Any, ...], errors: list[str]) -> None:
    if observed is None:
        _record_error(errors, path, "must be finite")
        return
    if abs(observed - expected) > TOLERANCE:
        _record_error(errors, path, f"expected {expected!r}, got {observed!r}")


def _validate_aggregate(
    payload: dict[str, Any],
    rows: list[Any],
    status_counts: dict[str, int],
    warnings: list[str],
    errors: list[str],
) -> None:
    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        _record_error(errors, ("aggregate",), "must be an object")
        return

    if aggregate.get("processed_frames") != len(rows):
        _record_error(errors, ("aggregate", "processed_frames"), f"must be {len(rows)!r}")
    for key, expected in status_counts.items():
        if aggregate.get(key) != expected:
            _record_error(errors, ("aggregate", key), f"must be {expected!r}")

    expected_counts: dict[str, int] = {key: 0 for key, _ in AGGREGATE_COUNT_KEYS}
    expected_counts["global_cell_count"] = 0
    expected_counts["global_finite_cell_count"] = 0
    expected_floats: dict[str, float] = {key: 0.0 for key in AGGREGATE_FLOAT_KEYS}

    for row in rows:
        if not isinstance(row, dict):
            continue
        expected_counts["global_cell_count"] += int(row.get("cell_count", 0))
        expected_counts["global_finite_cell_count"] += int(row.get("finite_cell_count", 0))
        for agg_key, row_key in AGGREGATE_COUNT_KEYS:
            expected_counts[agg_key] += int(row.get(row_key, 0))
        for key in AGGREGATE_FLOAT_KEYS:
            expected_floats[key] += float(row.get(key.replace("global_", ""), 0.0))

    for key, expected in expected_counts.items():
        actual = _coerce_nonnegative_int(aggregate.get(key))
        if actual is None:
            _record_error(errors, ("aggregate", key), "must be nonnegative int")
        elif actual != expected:
            _record_error(errors, ("aggregate", key), f"must be {expected!r}")

    for key, expected in expected_floats.items():
        observed = _coerce_finite_float(aggregate.get(key))
        _validate_floats(expected, observed, ("aggregate", key), errors)

    finite_cells = _coerce_nonnegative_int(aggregate.get("global_finite_cell_count")) or 0
    comp_zone_cells = _coerce_nonnegative_int(aggregate.get("global_compressive_zone_cell_count")) or 0

    for fraction_key, count_key, denom_key in AGGREGATE_FRACTION_KEYS:
        fraction = _coerce_finite_float(aggregate.get(fraction_key))
        count = _coerce_nonnegative_int(aggregate.get(count_key))
        denom = _coerce_nonnegative_int(aggregate.get(denom_key))
        if fraction is None:
            _record_error(errors, ("aggregate", fraction_key), "must be finite")
            continue
        if fraction < 0.0 or fraction > 1.0:
            _record_warning(warnings, ("aggregate", fraction_key), "outside [0,1]")
        expected = _expected_fraction(count, denom)
        if math.isnan(expected):
            continue
        if abs(fraction - expected) > TOLERANCE:
            _record_error(errors, ("aggregate", fraction_key), f"expected {expected!r}, got {fraction!r}")

    dominance_count_sum = (
        _coerce_nonnegative_int(aggregate.get("global_compressive_dominates_count"))
        or 0
    ) + (_coerce_nonnegative_int(aggregate.get("global_extensional_dominates_count")) or 0) + (
        _coerce_nonnegative_int(aggregate.get("global_dominance_tie_count")) or 0
    )
    if comp_zone_cells != dominance_count_sum:
        _record_error(errors, ("aggregate",), "dominance partition count mismatch")
    if aggregate.get("global_dominance_fraction_check_sum") is not None:
        if _coerce_nonnegative_int(aggregate.get("global_dominance_fraction_check_sum")) != dominance_count_sum:
            _record_warning(
                warnings,
                ("aggregate", "global_dominance_fraction_check_sum"),
                "should equal global_dominance partition sum",
            )

    if (
        _coerce_finite_float(aggregate.get("global_pi_sum")) is not None
        and _coerce_finite_float(aggregate.get("global_pi1_sum")) is not None
        and _coerce_finite_float(aggregate.get("global_pi2_sum")) is not None
        and _coerce_finite_float(aggregate.get("global_pi3_sum")) is not None
    ):
        expected = float(aggregate["global_pi1_sum"]) + float(aggregate["global_pi2_sum"]) + float(aggregate["global_pi3_sum"])
        observed = float(aggregate["global_pi_sum"])
        if abs(observed - expected) > TOLERANCE:
            _record_error(errors, ("aggregate", "global_pi_sum"), f"expected {expected!r}, got {observed!r}")

    for key in ("global_pi1_min", "global_pi1_max", "global_pi2_min", "global_pi2_max", "global_pi3_min", "global_pi3_max"):
        if _coerce_finite_float(aggregate.get(key)) is None and aggregate.get(key) is not None:
            _record_error(errors, ("aggregate", key), "must be finite if present")


    if (
        _coerce_finite_float(aggregate.get("global_lambda1_min")) is not None
        and _coerce_finite_float(aggregate.get("global_lambda1_max")) is not None
        and float(aggregate["global_lambda1_min"]) > float(aggregate["global_lambda1_max"])
    ):
        _record_error(errors, ("aggregate",), "global_lambda1_min > global_lambda1_max")
    if (
        _coerce_finite_float(aggregate.get("global_lambda2_min")) is not None
        and _coerce_finite_float(aggregate.get("global_lambda2_max")) is not None
        and float(aggregate["global_lambda2_min"]) > float(aggregate["global_lambda2_max"])
    ):
        _record_error(errors, ("aggregate",), "global_lambda2_min > global_lambda2_max")
    if (
        _coerce_finite_float(aggregate.get("global_lambda3_min")) is not None
        and _coerce_finite_float(aggregate.get("global_lambda3_max")) is not None
        and float(aggregate["global_lambda3_min"]) > float(aggregate["global_lambda3_max"])
    ):
        _record_error(errors, ("aggregate",), "global_lambda3_min > global_lambda3_max")


def _validate(payload: dict[str, Any]) -> tuple[list[str], list[str], dict[str, Any]]:
    warnings: list[str] = []
    errors: list[str] = []

    _check_control_card(payload, errors)
    _check_contract(payload, errors)
    _check_route(payload, errors)
    _check_status(payload, errors)
    _check_authority(payload, errors)
    _check_inputs(payload, warnings, errors)

    rows = payload.get("frames")
    ok_rows, status_counts = _validate_frames(payload, warnings, errors)
    if isinstance(rows, list):
        _validate_aggregate(payload, rows, status_counts, warnings, errors)

    details = {
        "status": payload.get("status"),
        "row_count": len(rows) if isinstance(rows, list) else 0,
        "ok_rows": ok_rows,
        "status_counts": status_counts,
    }
    return errors, warnings, details


def main() -> int:
    args = _parse_arguments()
    try:
        payload = _load_json(args.scan_json)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        output_payload = {
            "contract": CONTRACT,
            **CONTROL_CARD,
            "control_card": CONTROL_CARD,
            "route_decision": CHECK_ROUTE_DECISION,
            "status": ERROR_STATUS,
            "authority": {
                "candidate_only": True,
                "empirical_non_promoting": True,
                "truth_authority": False,
                "theorem_authority": False,
                "clay_authority": False,
                "runtime_authority": False,
                "promoted": False,
            },
            "input": {"scan_json": str(args.scan_json), "output_json": str(args.output_json)},
            "details": {},
            "warnings": [],
            "errors": [str(exc)],
            "changed_files": [str(args.scan_json)],
        }
        _write_json(args.output_json, output_payload, args.pretty)
        print(json.dumps(output_payload, sort_keys=True, indent=2 if args.pretty else None, ensure_ascii=False, allow_nan=False))
        return 1

    errors, warnings, details = _validate(payload)
    status = ERROR_STATUS if errors else OK_STATUS
    output_payload = {
        "contract": CONTRACT,
        "route_decision": CHECK_ROUTE_DECISION,
        "status": status,
        "authority": {
            "candidate_only": True,
            "empirical_non_promoting": True,
            "truth_authority": False,
            "theorem_authority": False,
            "clay_authority": False,
            "runtime_authority": False,
            "promoted": False,
        },
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
        "input": {"scan_json": str(args.scan_json), "output_json": str(args.output_json)},
        "details": details,
        "warnings": warnings,
        "errors": errors,
        "changed_files": [str(args.scan_json), str(args.output_json)],
    }
    _write_json(args.output_json, output_payload, args.pretty)
    print(json.dumps(output_payload, sort_keys=True, indent=2 if args.pretty else None, ensure_ascii=False, allow_nan=False))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
