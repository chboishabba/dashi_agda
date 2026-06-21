#!/usr/bin/env python3
"""Validate ns_pressure_eigenframe_gap_scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_pressure_eigenframe_gap_scan.py"
CONTRACT = "check_ns_pressure_eigenframe_gap_scan"
SCAN_CONTRACT = "ns_pressure_eigenframe_gap_scan"
SCAN_ROUTE_DECISION = "FAIL_CLOSED_NS_PRESSURE_EIGENFRAME_GAP_SCAN"
CHECK_ROUTE_DECISION = "FAIL_CLOSED_NS_PRESSURE_EIGENFRAME_GAP_SCAN_CHECK"

DEFAULT_SCAN_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_pressure_eigenframe_gap_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "check_ns_pressure_eigenframe_gap_scan_N128_20260621.json"
)

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
MISSING_REQUIRED_STATUS = "missing_required_field"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, MISSING_REQUIRED_STATUS, ERROR_STATUS}
TOLERANCE = 1.0e-12
CHECK_CARD_KEYS = ("O", "R", "C", "S", "L", "P", "G", "F")

CONTROL_CARD = {
    "O": "Validate spectral pressure-eigenframe gap scan output schema and arithmetic.",
    "R": (
        "Validate per-frame gap-row telemetry, threshold accumulation, and aggregate consistency "
        "for pressure Hessian off-diagonal projections in the strain eigenframe."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed checker: malformed schema, arithmetic drift, or invariant failures are errors.",
    "L": "Load scan JSON, validate control card + authority + per-row + aggregate invariants, and emit checker status.",
    "P": CHECK_ROUTE_DECISION,
    "G": "Checker is empirical and does not add theorem-level claims.",
    "F": "Any malformed field or arithmetic mismatch is treated as a hard failure.",
}

BENIGN_WARNING_SUFFIXES = (
    "velocity_snapshots axis-1 channel layout detected",
    "velocity_snapshots trailing channel layout detected",
    "velocity_snapshots last-axis channel layout detected",
    "velocity fallback axis-1 channel layout detected",
    "velocity fallback trailing channel layout detected",
    "converted legacy (T,N,N,N,3) velocity layout to components",
    "pressure_snapshots axis-1 singleton component axis detected",
    "pressure_snapshots trailing singleton component axis detected",
    "pressure last-axis singleton component axis detected",
    "domain_length unavailable; using fallback 6.283185307179586",
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--scan-json",
        type=Path,
        default=DEFAULT_SCAN_JSON,
        help="Path to ns_pressure_eigenframe_gap_scan output JSON.",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT_JSON,
        help="Path for checker output JSON.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print checker output.")
    return parser.parse_args()


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing scan json: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"scan json must be object: {path}")
    return payload


def _write_json(path: Path, payload: dict[str, Any], pretty: bool) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if pretty:
        text = json.dumps(payload, sort_keys=True, indent=2, allow_nan=False) + "\n"
    else:
        text = json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False) + "\n"
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


def _coerce_nonempty_str(value: Any) -> str | None:
    if not isinstance(value, str):
        return None
    text = value.strip()
    return text if text else None


def _coerce_bool(value: Any) -> bool | None:
    return value if isinstance(value, bool) else None


def _coerce_nonnegative_int(value: Any) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if isinstance(value, float) and value.is_integer():
        return int(value) if value >= 0.0 else None
    if isinstance(value, str):
        try:
            parsed = float(value.strip())
        except ValueError:
            return None
        if not math.isfinite(parsed) or not parsed.is_integer():
            return None
        return int(parsed) if parsed >= 0.0 else None
    return None


def _coerce_finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _fraction(numerator: int, denominator: int) -> float:
    if denominator <= 0:
        return 0.0
    return float(numerator) / float(denominator)


def _threshold_key(raw: Any) -> float | None:
    value = _coerce_finite_float(raw)
    if value is None or value < 0.0:
        return None
    return float(f"{float(value):.12g}")


def _is_benign_warning(value: Any) -> bool:
    if not isinstance(value, str):
        return False
    return any(value.endswith(suffix) or value == suffix for suffix in BENIGN_WARNING_SUFFIXES)


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
        value = _coerce_bool(authority.get(key))
        if value is None:
            _record_error(errors, ("authority", key), "must be bool")
        elif value is not expected_value:
            _record_error(errors, ("authority", key), f"must be {expected_value!r}")


def _check_inputs(payload: dict[str, Any], warnings: list[str], errors: list[str]) -> list[float]:
    inputs = payload.get("inputs")
    if not isinstance(inputs, dict):
        _record_error(errors, ("inputs",), "must be an object")
        return []

    if _coerce_nonempty_str(inputs.get("raw_archive")) is None:
        _record_error(errors, ("inputs", "raw_archive"), "must be non-empty string")

    frame = inputs.get("frame")
    if frame is not None and _coerce_nonnegative_int(frame) is None:
        _record_error(errors, ("inputs", "frame"), "must be null or nonnegative int")

    frame_limit = inputs.get("frame_limit")
    if frame_limit is not None and _coerce_nonnegative_int(frame_limit) is None:
        _record_error(errors, ("inputs", "frame_limit"), "must be null or nonnegative int")

    zero_eps = _coerce_finite_float(inputs.get("zero_eps"))
    if zero_eps is None or zero_eps < 0.0:
        _record_error(errors, ("inputs", "zero_eps"), "must be finite nonnegative float")

    raw_thresholds = inputs.get("delta1_thresholds")
    thresholds: list[float] = []
    if not isinstance(raw_thresholds, list) or not raw_thresholds:
        _record_error(errors, ("inputs", "delta1_thresholds"), "must be a non-empty list")
        return thresholds
    for index, value in enumerate(raw_thresholds):
        parsed = _coerce_finite_float(value)
        if parsed is None or parsed < 0.0:
            _record_error(errors, ("inputs", "delta1_thresholds", index), "must be finite nonnegative float")
            continue
        thresholds.append(float(parsed))
    thresholds = sorted(set(_threshold_key(t) or 0.0 for t in thresholds))
    if not thresholds:
        _record_error(errors, ("inputs", "delta1_thresholds"), "no usable thresholds")
    return thresholds


def _check_proxy_fields(
    row: dict[str, Any],
    cell_count: int,
    path: tuple[Any, ...],
    errors: list[str],
    warnings: list[str],
) -> None:
    for proxy in ("p12", "p13", "p23"):
        abs_sum = _coerce_finite_float(row.get(f"{proxy}_abs_sum"))
        abs_min = row.get(f"{proxy}_abs_min")
        abs_max = row.get(f"{proxy}_abs_max")
        abs_mean = _coerce_finite_float(row.get(f"{proxy}_abs_mean"))
        if abs_sum is None:
            _record_error(errors, path + (f"{proxy}_abs_sum",), "must be finite")
        if abs_sum is not None and abs_min is not None and _coerce_finite_float(abs_min) is None:
            _record_error(errors, path + (f"{proxy}_abs_min",), "must be finite or null")
        if abs_sum is not None and abs_max is not None and _coerce_finite_float(abs_max) is None:
            _record_error(errors, path + (f"{proxy}_abs_max",), "must be finite or null")
        if abs_mean is None:
            _record_error(errors, path + (f"{proxy}_abs_mean",), "must be finite")

        scaled_sum = _coerce_finite_float(row.get(f"{proxy}_scaled_sum"))
        scaled_min = row.get(f"{proxy}_scaled_min")
        scaled_max = row.get(f"{proxy}_scaled_max")
        scaled_mean = _coerce_finite_float(row.get(f"{proxy}_scaled_mean"))
        scaled_ge_one_count = _coerce_nonnegative_int(row.get(f"{proxy}_scaled_ge_one_count"))
        scaled_ge_one_fraction = _coerce_finite_float(row.get(f"{proxy}_scaled_ge_one_fraction"))
        if scaled_sum is None:
            _record_error(errors, path + (f"{proxy}_scaled_sum",), "must be finite")
        if scaled_sum is not None and scaled_min is not None and _coerce_finite_float(scaled_min) is None:
            _record_error(errors, path + (f"{proxy}_scaled_min",), "must be finite or null")
        if scaled_sum is not None and scaled_max is not None and _coerce_finite_float(scaled_max) is None:
            _record_error(errors, path + (f"{proxy}_scaled_max",), "must be finite or null")
        if scaled_mean is None:
            _record_error(errors, path + (f"{proxy}_scaled_mean",), "must be finite")
        if scaled_ge_one_count is None and cell_count > 0:
            _record_error(errors, path + (f"{proxy}_scaled_ge_one_count",), "must be nonnegative int")
        if scaled_ge_one_fraction is None:
            _record_error(errors, path + (f"{proxy}_scaled_ge_one_fraction",), "must be finite")

        if cell_count == 0:
            if abs_min is not None:
                _record_warning(warnings, path + (f"{proxy}_abs_min",), "must be null when cell_count is 0")
            if abs_max is not None:
                _record_warning(warnings, path + (f"{proxy}_abs_max",), "must be null when cell_count is 0")
            if scaled_min is not None:
                _record_warning(warnings, path + (f"{proxy}_scaled_min",), "must be null when cell_count is 0")
            if scaled_max is not None:
                _record_warning(warnings, path + (f"{proxy}_scaled_max",), "must be null when cell_count is 0")
            if abs_mean is not None and abs(abs_mean) > TOLERANCE:
                _record_warning(warnings, path + (f"{proxy}_abs_mean",), "mean should be 0.0 when cell_count is 0")
            if scaled_mean is not None and abs(scaled_mean) > TOLERANCE:
                _record_warning(warnings, path + (f"{proxy}_scaled_mean",), "mean should be 0.0 when cell_count is 0")
            if scaled_ge_one_count not in (None, 0):
                _record_error(errors, path + (f"{proxy}_scaled_ge_one_count",), "must be 0 when cell_count is 0")
            if scaled_ge_one_count == 0 and scaled_ge_one_fraction != 0.0:
                _record_error(errors, path + (f"{proxy}_scaled_ge_one_fraction",), "must be 0.0 when cell_count is 0")
            if abs_sum is not None and abs_sum != 0.0:
                _record_warning(warnings, path + (f"{proxy}_abs_sum",), "sum should be 0.0 when cell_count is 0")
            if scaled_sum is not None and scaled_sum != 0.0:
                _record_warning(warnings, path + (f"{proxy}_scaled_sum",), "sum should be 0.0 when cell_count is 0")
            if abs_mean is not None and abs_mean != 0.0:
                _record_warning(warnings, path + (f"{proxy}_abs_mean",), "mean should be 0.0 when cell_count is 0")
            if scaled_mean is not None and scaled_mean != 0.0:
                _record_warning(warnings, path + (f"{proxy}_scaled_mean",), "mean should be 0.0 when cell_count is 0")
        else:
            if abs_min is None or abs_max is None:
                _record_error(errors, path + (f"{proxy}_abs_min",), "must be finite when cell_count > 0")
            elif abs_min > abs_max:
                _record_error(errors, path + (f"{proxy}_abs_min",), "abs_min must not exceed abs_max")
            if scaled_min is None or scaled_max is None:
                _record_error(errors, path + (f"{proxy}_scaled_min",), "must be finite when cell_count > 0")
            elif scaled_min > scaled_max:
                _record_error(errors, path + (f"{proxy}_scaled_min",), "scaled_min must not exceed scaled_max")
            if abs_sum is not None and abs_mean is not None:
                expected = _fraction(cell_count, 1)
                expected = abs_sum / float(cell_count)
                if abs(abs_mean - expected) > TOLERANCE:
                    _record_error(errors, path + (f"{proxy}_abs_mean",), f"must equal {expected:.17g}, got {abs_mean:.17g}")
            if scaled_sum is not None and scaled_mean is not None:
                expected = scaled_sum / float(cell_count)
                if abs(scaled_mean - expected) > TOLERANCE:
                    _record_error(errors, path + (f"{proxy}_scaled_mean",), f"must equal {expected:.17g}, got {scaled_mean:.17g}")
            if scaled_ge_one_count is not None and scaled_ge_one_count > cell_count:
                _record_error(errors, path + (f"{proxy}_scaled_ge_one_count",), "cannot exceed cell_count")

            if scaled_ge_one_fraction is not None:
                expected = _fraction(int(scaled_ge_one_count or 0), int(cell_count))
                if abs(scaled_ge_one_fraction - expected) > TOLERANCE:
                    _record_error(
                        errors,
                        path + (f"{proxy}_scaled_ge_one_fraction",),
                        f"must equal {expected:.17g}, got {scaled_ge_one_fraction:.17g}",
                    )


def _validate_gap_row(
    row: dict[str, Any],
    frame_index: int,
    gap_index: int,
    compressive_count: int,
    warnings: list[str],
    errors: list[str],
) -> tuple[float, int]:
    threshold = _threshold_key(row.get("delta1_threshold"))
    if threshold is None:
        _record_error(errors, ("frames", frame_index, "gap_threshold_rows", gap_index, "delta1_threshold"), "must be finite nonnegative")
        return 0.0, 0
    cell_count = _coerce_nonnegative_int(row.get("cell_count"))
    if cell_count is None:
        _record_error(errors, ("frames", frame_index, "gap_threshold_rows", gap_index, "cell_count"), "must be nonnegative int")
        return threshold, 0
    if cell_count > compressive_count:
        _record_error(errors, ("frames", frame_index, "gap_threshold_rows", gap_index, "cell_count"), "cannot exceed frame compressive_zone_cell_count")

    expected_zone_fraction = _fraction(cell_count, compressive_count)
    observed_zone_fraction = _coerce_finite_float(row.get("zone_fraction"))
    if observed_zone_fraction is None:
        _record_error(errors, ("frames", frame_index, "gap_threshold_rows", gap_index, "zone_fraction"), "must be finite")
    elif abs(observed_zone_fraction - expected_zone_fraction) > TOLERANCE:
        _record_error(
            errors,
            ("frames", frame_index, "gap_threshold_rows", gap_index, "zone_fraction"),
            f"must equal {expected_zone_fraction:.17g}, got {observed_zone_fraction:.17g}",
        )

    _check_proxy_fields(
        row=row,
        cell_count=int(cell_count),
        path=("frames", frame_index, "gap_threshold_rows", gap_index),
        errors=errors,
        warnings=warnings,
    )
    return threshold, int(cell_count)


def _validate_frame_row(
    row: dict[str, Any],
    index: int,
    thresholds: list[float],
    warnings: list[str],
    errors: list[str],
) -> dict[str, Any]:
    status = row.get("status")
    if status not in ALLOWED_STATUSES:
        _record_error(errors, ("frames", index, "status"), "must be one of ok|partial|missing_required_field|error")
        status = ERROR_STATUS

    if _coerce_nonnegative_int(row.get("frame")) is None:
        _record_error(errors, ("frames", index, "frame"), "must be nonnegative int")
    if _coerce_nonnegative_int(row.get("snapshot_index")) is None:
        _record_error(errors, ("frames", index, "snapshot_index"), "must be nonnegative int")

    for key in ("raw_archive", "velocity_source", "pressure_source", "pressure_hessian_source"):
        if _coerce_nonempty_str(row.get(key)) is None:
            _record_error(errors, ("frames", index, key), "must be non-empty string")
    if row.get("pressure_hessian_source") != "spectral_pressure_hessian":
        _record_warning(warnings, ("frames", index, "pressure_hessian_source"), "expected spectral_pressure_hessian")

    if status == ERROR_STATUS:
        row_errors = row.get("errors")
        if not isinstance(row_errors, list) or not row_errors:
            _record_error(errors, ("frames", index, "errors"), "error rows must include non-empty errors list")
        return {"status": status, "compressive_zone_cell_count": 0}

    cell_count = _coerce_nonnegative_int(row.get("cell_count"))
    finite_count = _coerce_nonnegative_int(row.get("finite_cell_count"))
    if cell_count is None:
        _record_error(errors, ("frames", index, "cell_count"), "must be nonnegative int")
    if finite_count is None:
        _record_error(errors, ("frames", index, "finite_cell_count"), "must be nonnegative int")
    if isinstance(cell_count, int) and isinstance(finite_count, int) and finite_count > cell_count:
        _record_error(errors, ("frames", index), "finite_cell_count cannot exceed cell_count")

    if status == MISSING_REQUIRED_STATUS:
        row_errors = row.get("errors")
        if not isinstance(row_errors, list) or not row_errors:
            _record_error(errors, ("frames", index, "errors"), "missing-required rows should include non-empty errors list")

    l2_pos = _coerce_nonnegative_int(row.get("lambda2_positive_count"))
    l2_neg = _coerce_nonnegative_int(row.get("lambda2_negative_count"))
    l2_zero = _coerce_nonnegative_int(row.get("lambda2_zero_count"))
    if isinstance(finite_count, int) and l2_pos is not None and l2_neg is not None and l2_zero is not None:
        if l2_pos + l2_neg + l2_zero != finite_count:
            _record_error(errors, ("frames", index), "lambda2 counts must partition finite_cell_count")

    l2_pos_f = _coerce_finite_float(row.get("lambda2_positive_fraction"))
    l2_neg_f = _coerce_finite_float(row.get("lambda2_negative_fraction"))
    l2_zero_f = _coerce_finite_float(row.get("lambda2_zero_fraction"))
    if l2_pos_f is None:
        _record_error(errors, ("frames", index, "lambda2_positive_fraction"), "must be finite")
    if l2_neg_f is None:
        _record_error(errors, ("frames", index, "lambda2_negative_fraction"), "must be finite")
    if l2_zero_f is None:
        _record_error(errors, ("frames", index, "lambda2_zero_fraction"), "must be finite")
    if l2_pos is not None and finite_count is not None and l2_pos_f is not None:
        expected = _fraction(l2_pos, finite_count)
        if abs(l2_pos_f - expected) > TOLERANCE:
            _record_error(
                errors,
                ("frames", index, "lambda2_positive_fraction"),
                f"must equal {expected:.17g}, got {l2_pos_f:.17g}",
            )
    if l2_neg is not None and finite_count is not None and l2_neg_f is not None:
        expected = _fraction(l2_neg, finite_count)
        if abs(l2_neg_f - expected) > TOLERANCE:
            _record_error(
                errors,
                ("frames", index, "lambda2_negative_fraction"),
                f"must equal {expected:.17g}, got {l2_neg_f:.17g}",
            )
    if l2_zero is not None and finite_count is not None and l2_zero_f is not None:
        expected = _fraction(l2_zero, finite_count)
        if abs(l2_zero_f - expected) > TOLERANCE:
            _record_error(
                errors,
                ("frames", index, "lambda2_zero_fraction"),
                f"must equal {expected:.17g}, got {l2_zero_f:.17g}",
            )

    compressive_count = _coerce_nonnegative_int(row.get("compressive_zone_cell_count")) or 0
    if isinstance(finite_count, int) and compressive_count > finite_count:
        _record_error(errors, ("frames", index, "compressive_zone_cell_count"), "cannot exceed finite_cell_count")

    delta1_sum = _coerce_finite_float(row.get("delta1_sum"))
    delta1_mean = _coerce_finite_float(row.get("delta1_mean"))
    delta1_min = row.get("delta1_min")
    delta1_max = row.get("delta1_max")
    if delta1_sum is None:
        _record_error(errors, ("frames", index, "delta1_sum"), "must be finite")
    if delta1_mean is None:
        _record_error(errors, ("frames", index, "delta1_mean"), "must be finite")

    if compressive_count > 0:
        if _coerce_finite_float(delta1_min) is None:
            _record_error(errors, ("frames", index, "delta1_min"), "must be finite when compressive cells exist")
        if _coerce_finite_float(delta1_max) is None:
            _record_error(errors, ("frames", index, "delta1_max"), "must be finite when compressive cells exist")
        if delta1_sum is not None and delta1_mean is not None:
            expected = delta1_sum / float(compressive_count)
            if abs(delta1_mean - expected) > TOLERANCE:
                _record_error(
                    errors,
                    ("frames", index, "delta1_mean"),
                    f"must equal {expected:.17g}, got {delta1_mean:.17g}",
                )
        if _coerce_finite_float(delta1_min) is not None and _coerce_finite_float(delta1_max) is not None:
            if float(delta1_min) > float(delta1_max):
                _record_error(errors, ("frames", index, "delta1"), "delta1_min cannot exceed delta1_max")
    else:
        if delta1_min is not None:
            _record_warning(warnings, ("frames", index, "delta1_min"), "must be null when no compressive cells")
        if delta1_max is not None:
            _record_warning(warnings, ("frames", index, "delta1_max"), "must be null when no compressive cells")
        if delta1_sum not in (0.0, None) and abs(float(delta1_sum or 0.0)) > TOLERANCE:
            _record_warning(warnings, ("frames", index, "delta1_sum"), "expected 0.0 when no compressive cells")
        if delta1_mean not in (0.0, None) and abs(float(delta1_mean or 0.0)) > TOLERANCE:
            _record_warning(warnings, ("frames", index, "delta1_mean"), "expected 0.0 when no compressive cells")

    for proxy in ("p12", "p13", "p23"):
        abs_sum = _coerce_finite_float(row.get(f"{proxy}_abs_sum"))
        scaled_sum = _coerce_finite_float(row.get(f"{proxy}_scaled_sum"))
        if compressive_count > 0:
            if abs_sum is not None:
                expected = _coerce_finite_float(row.get(f"{proxy}_abs_mean"))
                if expected is None:
                    _record_error(errors, ("frames", index, f"{proxy}_abs_mean"), "must be finite")
                else:
                    expected_mean = abs_sum / float(compressive_count)
                    if abs(expected - expected_mean) > TOLERANCE:
                        _record_error(
                            errors,
                            ("frames", index, f"{proxy}_abs_mean"),
                            f"must equal {expected_mean:.17g}, got {expected:.17g}",
                        )
            if scaled_sum is not None:
                scaled_mean = _coerce_finite_float(row.get(f"{proxy}_scaled_mean"))
                if scaled_mean is None:
                    _record_error(errors, ("frames", index, f"{proxy}_scaled_mean"), "must be finite")
                else:
                    expected_scaled_mean = scaled_sum / float(compressive_count)
                    if abs(scaled_mean - expected_scaled_mean) > TOLERANCE:
                        _record_error(
                            errors,
                            ("frames", index, f"{proxy}_scaled_mean"),
                            f"must equal {expected_scaled_mean:.17g}, got {scaled_mean:.17g}",
                        )
        else:
            for key in (f"{proxy}_abs_sum", f"{proxy}_scaled_sum"):
                value = _coerce_finite_float(row.get(key))
                if value not in (None, 0.0):
                    _record_warning(warnings, ("frames", index, key), "expected 0.0 when no compressive cells")

    if _coerce_finite_float(row.get("pressure_hessian_norm")) is None:
        _record_error(errors, ("frames", index, "pressure_hessian_norm"), "must be finite")
    if _coerce_finite_float(row.get("pressure_hessian_frobenius_norm")) is None:
        _record_error(errors, ("frames", index, "pressure_hessian_frobenius_norm"), "must be finite")

    if _coerce_finite_float(row.get("pressure_hessian_norm")) != _coerce_finite_float(row.get("pressure_hessian_frobenius_norm")):
        norm = _coerce_finite_float(row.get("pressure_hessian_norm"))
        norm_f = _coerce_finite_float(row.get("pressure_hessian_frobenius_norm"))
        if norm is not None and norm_f is not None and abs(norm - norm_f) > TOLERANCE:
            _record_error(
                errors,
                ("frames", index, "pressure_hessian_norm"),
                f"must equal pressure_hessian_frobenius_norm: {norm_f:.17g} vs {norm:.17g}",
            )

    _check_proxy_fields(
        row=row,
        cell_count=compressive_count,
        path=("frames", index),
        errors=errors,
        warnings=warnings,
    )

    gap_rows = row.get("gap_threshold_rows")
    if not isinstance(gap_rows, list):
        _record_error(errors, ("frames", index, "gap_threshold_rows"), "must be a list")
        return {"status": status, "compressive_zone_cell_count": compressive_count}

    seen_thresholds: set[float] = set()
    for gap_index, gap_row in enumerate(gap_rows):
        if not isinstance(gap_row, dict):
            _record_error(errors, ("frames", index, "gap_threshold_rows", gap_index), "must be an object")
            continue
        threshold, gap_cells = _validate_gap_row(gap_row, index, gap_index, compressive_count, warnings, errors)
        if threshold is not None and threshold >= 0.0:
            seen_thresholds.add(float(threshold))
        if gap_cells > compressive_count:
            _record_error(
                errors,
                ("frames", index, "gap_threshold_rows", gap_index),
                f"gap cell_count cannot exceed frame compressive zone ({compressive_count})",
            )

    for threshold in thresholds:
        if threshold not in seen_thresholds:
            _record_warning(warnings, ("frames", index, "gap_threshold_rows"), f"missing declared threshold {threshold}")

    for i in range(1, len(gap_rows)):
        left_threshold = _threshold_key(gap_rows[i - 1].get("delta1_threshold") if isinstance(gap_rows[i - 1], dict) else None)
        right_threshold = _threshold_key(gap_rows[i].get("delta1_threshold") if isinstance(gap_rows[i], dict) else None)
        if left_threshold is not None and right_threshold is not None and right_threshold < left_threshold:
            _record_warning(warnings, ("frames", index, "gap_threshold_rows"), "thresholds should be nondecreasing")

    return {"status": status, "compressive_zone_cell_count": compressive_count}


def _collect_gap_buckets(rows: list[dict[str, Any]]) -> dict[float, dict[str, Any]]:
    buckets: dict[float, dict[str, Any]] = {}
    for row in rows:
        gap_rows = row.get("gap_threshold_rows")
        if not isinstance(gap_rows, list):
            continue
        for entry in gap_rows:
            if not isinstance(entry, dict):
                continue
            threshold = _threshold_key(entry.get("delta1_threshold"))
            if threshold is None:
                continue
            bucket = buckets.setdefault(
                threshold,
                {
                    "cell_count": 0,
                    "p12_abs_sum": 0.0,
                    "p13_abs_sum": 0.0,
                    "p23_abs_sum": 0.0,
                    "p12_scaled_sum": 0.0,
                    "p13_scaled_sum": 0.0,
                    "p23_scaled_sum": 0.0,
                    "p12_abs_min": None,
                    "p12_abs_max": None,
                    "p13_abs_min": None,
                    "p13_abs_max": None,
                    "p23_abs_min": None,
                    "p23_abs_max": None,
                    "p12_scaled_min": None,
                    "p12_scaled_max": None,
                    "p13_scaled_min": None,
                    "p13_scaled_max": None,
                    "p23_scaled_min": None,
                    "p23_scaled_max": None,
                    "p12_scaled_ge_one_count": 0,
                    "p13_scaled_ge_one_count": 0,
                    "p23_scaled_ge_one_count": 0,
                },
            )
            bucket["cell_count"] += int(_coerce_nonnegative_int(entry.get("cell_count")) or 0)
            for key in (
                "p12_abs_sum",
                "p13_abs_sum",
                "p23_abs_sum",
                "p12_scaled_sum",
                "p13_scaled_sum",
                "p23_scaled_sum",
            ):
                bucket[key] += float(_coerce_finite_float(entry.get(key)) or 0.0)

            for key in ("p12_scaled_ge_one_count", "p13_scaled_ge_one_count", "p23_scaled_ge_one_count"):
                bucket[key] += int(_coerce_nonnegative_int(entry.get(key)) or 0)

            for key in (
                "p12_abs_min",
                "p13_abs_min",
                "p23_abs_min",
                "p12_scaled_min",
                "p13_scaled_min",
                "p23_scaled_min",
                "p12_abs_max",
                "p13_abs_max",
                "p23_abs_max",
                "p12_scaled_max",
                "p13_scaled_max",
                "p23_scaled_max",
            ):
                value = _coerce_finite_float(entry.get(key))
                if value is None:
                    continue
                if bucket[key] is None:
                    bucket[key] = value
                elif "_min" in key:
                    if value < float(bucket[key]):
                        bucket[key] = value
                else:
                    if value > float(bucket[key]):
                        bucket[key] = value
    return buckets


def _validate_aggregate(
    payload: dict[str, Any],
    rows: list[dict[str, Any]],
    warnings: list[str],
    errors: list[str],
) -> None:
    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        _record_error(errors, ("aggregate",), "must be an object")
        return

    if aggregate.get("processed_frames") != len(rows):
        _record_error(errors, ("aggregate", "processed_frames"), f"must be {len(rows)!r}")

    expected_status_counts = {
        "ok_frames": 0,
        "partial_frames": 0,
        "missing_frames": 0,
        "error_frames": 0,
    }
    for row in rows:
        status = row.get("status")
        if status == OK_STATUS:
            expected_status_counts["ok_frames"] += 1
        elif status == PARTIAL_STATUS:
            expected_status_counts["partial_frames"] += 1
        elif status == MISSING_REQUIRED_STATUS:
            expected_status_counts["missing_frames"] += 1
        else:
            expected_status_counts["error_frames"] += 1

    for key, expected in expected_status_counts.items():
        if aggregate.get(key) != expected:
            _record_error(errors, ("aggregate", key), f"must be {expected!r}")

    expected_cell_count = 0
    expected_finite_count = 0
    expected_l2_pos = 0
    expected_l2_neg = 0
    expected_l2_zero = 0
    expected_compressive = 0
    expected_delta1_sum = 0.0
    expected_p12_abs_sum = 0.0
    expected_p13_abs_sum = 0.0
    expected_p23_abs_sum = 0.0
    expected_p12_scaled_sum = 0.0
    expected_p13_scaled_sum = 0.0
    expected_p23_scaled_sum = 0.0
    expected_p12_ge_one = 0
    expected_p13_ge_one = 0
    expected_p23_ge_one = 0

    expected_delta1_min = None
    expected_delta1_max = None
    expected_p12_abs_min = None
    expected_p12_abs_max = None
    expected_p13_abs_min = None
    expected_p13_abs_max = None
    expected_p23_abs_min = None
    expected_p23_abs_max = None
    expected_p12_scaled_min = None
    expected_p12_scaled_max = None
    expected_p13_scaled_min = None
    expected_p13_scaled_max = None
    expected_p23_scaled_min = None
    expected_p23_scaled_max = None

    for row in rows:
        if not isinstance(row, dict):
            continue
        expected_cell_count += int(_coerce_nonnegative_int(row.get("cell_count")) or 0)
        expected_finite_count += int(_coerce_nonnegative_int(row.get("finite_cell_count")) or 0)
        expected_l2_pos += int(_coerce_nonnegative_int(row.get("lambda2_positive_count")) or 0)
        expected_l2_neg += int(_coerce_nonnegative_int(row.get("lambda2_negative_count")) or 0)
        expected_l2_zero += int(_coerce_nonnegative_int(row.get("lambda2_zero_count")) or 0)

        compressive = int(_coerce_nonnegative_int(row.get("compressive_zone_cell_count")) or 0)
        expected_compressive += compressive

        row_delta1_sum = _coerce_finite_float(row.get("delta1_sum"))
        if row_delta1_sum is not None:
            expected_delta1_sum += row_delta1_sum

        for proxy, target in (
            ("p12", "p12_abs_sum"),
            ("p13", "p13_abs_sum"),
            ("p23", "p23_abs_sum"),
        ):
            value = _coerce_finite_float(row.get(f"{proxy}_abs_sum"))
            if value is not None:
                if target == "p12_abs_sum":
                    expected_p12_abs_sum += value
                elif target == "p13_abs_sum":
                    expected_p13_abs_sum += value
                else:
                    expected_p23_abs_sum += value
            min_value = _coerce_finite_float(row.get(f"{proxy}_abs_min"))
            max_value = _coerce_finite_float(row.get(f"{proxy}_abs_max"))
            if compressive > 0:
                if min_value is None or max_value is None:
                    _record_error(errors, ("aggregate",), "frame min/max needed for global recomputation")
                else:
                    if proxy == "p12":
                        expected_p12_abs_min = min_value if expected_p12_abs_min is None else min(expected_p12_abs_min, min_value)
                        expected_p12_abs_max = max_value if expected_p12_abs_max is None else max(expected_p12_abs_max, max_value)
                    elif proxy == "p13":
                        expected_p13_abs_min = min_value if expected_p13_abs_min is None else min(expected_p13_abs_min, min_value)
                        expected_p13_abs_max = max_value if expected_p13_abs_max is None else max(expected_p13_abs_max, max_value)
                    else:
                        expected_p23_abs_min = min_value if expected_p23_abs_min is None else min(expected_p23_abs_min, min_value)
                        expected_p23_abs_max = max_value if expected_p23_abs_max is None else max(expected_p23_abs_max, max_value)

        for proxy, target in (
            ("p12", "p12_scaled_sum"),
            ("p13", "p13_scaled_sum"),
            ("p23", "p23_scaled_sum"),
        ):
            value = _coerce_finite_float(row.get(f"{proxy}_scaled_sum"))
            if value is not None:
                if target == "p12_scaled_sum":
                    expected_p12_scaled_sum += value
                elif target == "p13_scaled_sum":
                    expected_p13_scaled_sum += value
                else:
                    expected_p23_scaled_sum += value
            min_value = _coerce_finite_float(row.get(f"{proxy}_scaled_min"))
            max_value = _coerce_finite_float(row.get(f"{proxy}_scaled_max"))
            if compressive > 0:
                if min_value is None or max_value is None:
                    _record_error(errors, ("aggregate",), "frame scaled min/max needed for global recomputation")
                else:
                    if proxy == "p12":
                        expected_p12_scaled_min = min_value if expected_p12_scaled_min is None else min(expected_p12_scaled_min, min_value)
                        expected_p12_scaled_max = max_value if expected_p12_scaled_max is None else max(expected_p12_scaled_max, max_value)
                    elif proxy == "p13":
                        expected_p13_scaled_min = min_value if expected_p13_scaled_min is None else min(expected_p13_scaled_min, min_value)
                        expected_p13_scaled_max = max_value if expected_p13_scaled_max is None else max(expected_p13_scaled_max, max_value)
                    else:
                        expected_p23_scaled_min = min_value if expected_p23_scaled_min is None else min(expected_p23_scaled_min, min_value)
                        expected_p23_scaled_max = max_value if expected_p23_scaled_max is None else max(expected_p23_scaled_max, max_value)

        expected_p12_ge_one += int(_coerce_nonnegative_int(row.get("p12_scaled_ge_one_count")) or 0)
        expected_p13_ge_one += int(_coerce_nonnegative_int(row.get("p13_scaled_ge_one_count")) or 0)
        expected_p23_ge_one += int(_coerce_nonnegative_int(row.get("p23_scaled_ge_one_count")) or 0)

    expected_floats = (
        ("global_cell_count", float(expected_cell_count)),
        ("global_finite_cell_count", float(expected_finite_count)),
    )
    for key, expected in expected_floats:
        observed = _coerce_finite_float(aggregate.get(key))
        if observed is None or int(observed) != int(expected):
            _record_error(errors, ("aggregate", key), f"must be {expected!r}")

    if aggregate.get("global_lambda2_positive_count") != expected_l2_pos:
        _record_error(errors, ("aggregate", "global_lambda2_positive_count"), f"must be {expected_l2_pos!r}")
    if aggregate.get("global_lambda2_negative_count") != expected_l2_neg:
        _record_error(errors, ("aggregate", "global_lambda2_negative_count"), f"must be {expected_l2_neg!r}")
    if aggregate.get("global_lambda2_zero_count") != expected_l2_zero:
        _record_error(errors, ("aggregate", "global_lambda2_zero_count"), f"must be {expected_l2_zero!r}")
    if aggregate.get("global_compressive_zone_cell_count") != expected_compressive:
        _record_error(errors, ("aggregate", "global_compressive_zone_cell_count"), f"must be {expected_compressive!r}")

    observed_delta1_sum = _coerce_finite_float(aggregate.get("global_delta1_sum"))
    if observed_delta1_sum is None or abs(observed_delta1_sum - expected_delta1_sum) > TOLERANCE:
        _record_error(errors, ("aggregate", "global_delta1_sum"), f"must be {expected_delta1_sum!r}, got {observed_delta1_sum!r}")
    if abs((_coerce_finite_float(aggregate.get("global_p12_abs_sum") or 0.0)) - expected_p12_abs_sum) > TOLERANCE:
        observed = _coerce_finite_float(aggregate.get("global_p12_abs_sum"))
        _record_error(errors, ("aggregate", "global_p12_abs_sum"), f"must be {expected_p12_abs_sum!r}, got {observed!r}")
    if abs((_coerce_finite_float(aggregate.get("global_p13_abs_sum") or 0.0)) - expected_p13_abs_sum) > TOLERANCE:
        observed = _coerce_finite_float(aggregate.get("global_p13_abs_sum"))
        _record_error(errors, ("aggregate", "global_p13_abs_sum"), f"must be {expected_p13_abs_sum!r}, got {observed!r}")
    if abs((_coerce_finite_float(aggregate.get("global_p23_abs_sum") or 0.0)) - expected_p23_abs_sum) > TOLERANCE:
        observed = _coerce_finite_float(aggregate.get("global_p23_abs_sum"))
        _record_error(errors, ("aggregate", "global_p23_abs_sum"), f"must be {expected_p23_abs_sum!r}, got {observed!r}")
    if abs((_coerce_finite_float(aggregate.get("global_p12_scaled_sum") or 0.0)) - expected_p12_scaled_sum) > TOLERANCE:
        observed = _coerce_finite_float(aggregate.get("global_p12_scaled_sum"))
        _record_error(errors, ("aggregate", "global_p12_scaled_sum"), f"must be {expected_p12_scaled_sum!r}, got {observed!r}")
    if abs((_coerce_finite_float(aggregate.get("global_p13_scaled_sum") or 0.0)) - expected_p13_scaled_sum) > TOLERANCE:
        observed = _coerce_finite_float(aggregate.get("global_p13_scaled_sum"))
        _record_error(errors, ("aggregate", "global_p13_scaled_sum"), f"must be {expected_p13_scaled_sum!r}, got {observed!r}")
    if abs((_coerce_finite_float(aggregate.get("global_p23_scaled_sum") or 0.0)) - expected_p23_scaled_sum) > TOLERANCE:
        observed = _coerce_finite_float(aggregate.get("global_p23_scaled_sum"))
        _record_error(errors, ("aggregate", "global_p23_scaled_sum"), f"must be {expected_p23_scaled_sum!r}, got {observed!r}")

    if aggregate.get("global_p12_scaled_ge_one_count") != expected_p12_ge_one:
        _record_error(errors, ("aggregate", "global_p12_scaled_ge_one_count"), f"must be {expected_p12_ge_one!r}")
    if aggregate.get("global_p13_scaled_ge_one_count") != expected_p13_ge_one:
        _record_error(errors, ("aggregate", "global_p13_scaled_ge_one_count"), f"must be {expected_p13_ge_one!r}")
    if aggregate.get("global_p23_scaled_ge_one_count") != expected_p23_ge_one:
        _record_error(errors, ("aggregate", "global_p23_scaled_ge_one_count"), f"must be {expected_p23_ge_one!r}")

    expected_delta1_mean = _fraction(expected_delta1_sum if expected_compressive >= 0 else 0.0, expected_compressive)
    observed_delta1_mean = _coerce_finite_float(aggregate.get("global_delta1_mean"))
    if observed_delta1_mean is None or abs(observed_delta1_mean - expected_delta1_mean) > TOLERANCE:
        _record_error(errors, ("aggregate", "global_delta1_mean"), f"must be {expected_delta1_mean:.17g}")

    expected_p12_abs_mean = _fraction(expected_p12_abs_sum, expected_compressive)
    observed_p12_abs_mean = _coerce_finite_float(aggregate.get("global_p12_abs_mean"))
    if observed_p12_abs_mean is None or abs(observed_p12_abs_mean - expected_p12_abs_mean) > TOLERANCE:
        _record_error(errors, ("aggregate", "global_p12_abs_mean"), f"must be {expected_p12_abs_mean:.17g}")
    expected_p13_abs_mean = _fraction(expected_p13_abs_sum, expected_compressive)
    observed_p13_abs_mean = _coerce_finite_float(aggregate.get("global_p13_abs_mean"))
    if observed_p13_abs_mean is None or abs(observed_p13_abs_mean - expected_p13_abs_mean) > TOLERANCE:
        _record_error(errors, ("aggregate", "global_p13_abs_mean"), f"must be {expected_p13_abs_mean:.17g}")
    expected_p23_abs_mean = _fraction(expected_p23_abs_sum, expected_compressive)
    observed_p23_abs_mean = _coerce_finite_float(aggregate.get("global_p23_abs_mean"))
    if observed_p23_abs_mean is None or abs(observed_p23_abs_mean - expected_p23_abs_mean) > TOLERANCE:
        _record_error(errors, ("aggregate", "global_p23_abs_mean"), f"must be {expected_p23_abs_mean:.17g}")

    expected_p12_scaled_mean = _fraction(expected_p12_scaled_sum, expected_compressive)
    observed_p12_scaled_mean = _coerce_finite_float(aggregate.get("global_p12_scaled_mean"))
    if observed_p12_scaled_mean is None or abs(observed_p12_scaled_mean - expected_p12_scaled_mean) > TOLERANCE:
        _record_error(errors, ("aggregate", "global_p12_scaled_mean"), f"must be {expected_p12_scaled_mean:.17g}")
    expected_p13_scaled_mean = _fraction(expected_p13_scaled_sum, expected_compressive)
    observed_p13_scaled_mean = _coerce_finite_float(aggregate.get("global_p13_scaled_mean"))
    if observed_p13_scaled_mean is None or abs(observed_p13_scaled_mean - expected_p13_scaled_mean) > TOLERANCE:
        _record_error(errors, ("aggregate", "global_p13_scaled_mean"), f"must be {expected_p13_scaled_mean:.17g}")
    expected_p23_scaled_mean = _fraction(expected_p23_scaled_sum, expected_compressive)
    observed_p23_scaled_mean = _coerce_finite_float(aggregate.get("global_p23_scaled_mean"))
    if observed_p23_scaled_mean is None or abs(observed_p23_scaled_mean - expected_p23_scaled_mean) > TOLERANCE:
        _record_error(errors, ("aggregate", "global_p23_scaled_mean"), f"must be {expected_p23_scaled_mean:.17g}")

    expected_l2_pos_f = _fraction(expected_l2_pos, expected_finite_count)
    expected_l2_neg_f = _fraction(expected_l2_neg, expected_finite_count)
    expected_l2_zero_f = _fraction(expected_l2_zero, expected_finite_count)
    for key, expected in (
        ("global_lambda2_positive_fraction", expected_l2_pos_f),
        ("global_lambda2_negative_fraction", expected_l2_neg_f),
        ("global_lambda2_zero_fraction", expected_l2_zero_f),
    ):
        observed = _coerce_finite_float(aggregate.get(key))
        if observed is None or abs(observed - expected) > TOLERANCE:
            _record_error(errors, ("aggregate", key), f"must be {expected:.17g}")

    expected_compressive_f = _fraction(expected_compressive, expected_finite_count)
    observed_compressive_f = _coerce_finite_float(aggregate.get("global_compressive_zone_fraction"))
    if observed_compressive_f is None or abs(observed_compressive_f - expected_compressive_f) > TOLERANCE:
        _record_error(errors, ("aggregate", "global_compressive_zone_fraction"), f"must be {expected_compressive_f:.17g}")

    expected_p12_ge_one_fraction = _fraction(expected_p12_ge_one, expected_compressive)
    observed_p12_ge_one_fraction = _coerce_finite_float(aggregate.get("global_p12_scaled_ge_one_fraction"))
    if observed_p12_ge_one_fraction is None or abs(observed_p12_ge_one_fraction - expected_p12_ge_one_fraction) > TOLERANCE:
        _record_error(errors, ("aggregate", "global_p12_scaled_ge_one_fraction"), f"must be {expected_p12_ge_one_fraction:.17g}")
    expected_p13_ge_one_fraction = _fraction(expected_p13_ge_one, expected_compressive)
    observed_p13_ge_one_fraction = _coerce_finite_float(aggregate.get("global_p13_scaled_ge_one_fraction"))
    if observed_p13_ge_one_fraction is None or abs(observed_p13_ge_one_fraction - expected_p13_ge_one_fraction) > TOLERANCE:
        _record_error(errors, ("aggregate", "global_p13_scaled_ge_one_fraction"), f"must be {expected_p13_ge_one_fraction:.17g}")
    expected_p23_ge_one_fraction = _fraction(expected_p23_ge_one, expected_compressive)
    observed_p23_ge_one_fraction = _coerce_finite_float(aggregate.get("global_p23_scaled_ge_one_fraction"))
    if observed_p23_ge_one_fraction is None or abs(observed_p23_ge_one_fraction - expected_p23_ge_one_fraction) > TOLERANCE:
        _record_error(errors, ("aggregate", "global_p23_scaled_ge_one_fraction"), f"must be {expected_p23_ge_one_fraction:.17g}")

    if expected_compressive > 0:
        if _coerce_finite_float(aggregate.get("global_delta1_min")) is None:
            _record_error(errors, ("aggregate", "global_delta1_min"), "must be finite when compressive cells exist")
        if _coerce_finite_float(aggregate.get("global_delta1_max")) is None:
            _record_error(errors, ("aggregate", "global_delta1_max"), "must be finite when compressive cells exist")
        if _coerce_finite_float(aggregate.get("global_delta1_min")) is not None and _coerce_finite_float(aggregate.get("global_delta1_max")) is not None:
            if _coerce_finite_float(aggregate.get("global_delta1_min")) > _coerce_finite_float(aggregate.get("global_delta1_max")):
                _record_error(errors, ("aggregate", "global_delta1"), "global_delta1_min cannot exceed global_delta1_max")
        if expected_delta1_min is not None and _coerce_finite_float(aggregate.get("global_delta1_min")) is not None:
            if abs(_coerce_finite_float(aggregate.get("global_delta1_min")) - expected_delta1_min) > TOLERANCE:
                _record_error(errors, ("aggregate", "global_delta1_min"), f"must match frame minimum {expected_delta1_min:.17g}")
        if expected_delta1_max is not None and _coerce_finite_float(aggregate.get("global_delta1_max")) is not None:
            if abs(_coerce_finite_float(aggregate.get("global_delta1_max")) - expected_delta1_max) > TOLERANCE:
                _record_error(errors, ("aggregate", "global_delta1_max"), f"must match frame maximum {expected_delta1_max:.17g}")
    else:
        if aggregate.get("global_delta1_min") is not None:
            _record_warning(warnings, ("aggregate", "global_delta1_min"), "must be null when no compressive cells")
        if aggregate.get("global_delta1_max") is not None:
            _record_warning(warnings, ("aggregate", "global_delta1_max"), "must be null when no compressive cells")

    for proxy_key, expected_min, expected_max in (
        ("global_p12_abs_min", expected_p12_abs_min, expected_p12_abs_max),
        ("global_p13_abs_min", expected_p13_abs_min, expected_p13_abs_max),
        ("global_p23_abs_min", expected_p23_abs_min, expected_p23_abs_max),
        ("global_p12_scaled_min", expected_p12_scaled_min, expected_p12_scaled_max),
        ("global_p13_scaled_min", expected_p13_scaled_min, expected_p13_scaled_max),
        ("global_p23_scaled_min", expected_p23_scaled_min, expected_p23_scaled_max),
    ):
        observed_min = _coerce_finite_float(aggregate.get(f"{proxy_key}"))
        observed_max = _coerce_finite_float(aggregate.get(f"{proxy_key.replace('_min', '_max')}"))
        if expected_compressive > 0:
            if observed_min is None or observed_max is None:
                _record_error(errors, ("aggregate", proxy_key.replace("_min", "")), "must be finite when aggregate has compressive cells")
            elif observed_min > observed_max:
                _record_error(errors, ("aggregate", proxy_key.replace("_min", "")), "min cannot exceed max")
            if expected_min is not None and abs(observed_min - expected_min) > TOLERANCE:
                _record_error(errors, ("aggregate", proxy_key), f"must be {expected_min:.17g}")
            if expected_max is not None and abs(observed_max - expected_max) > TOLERANCE:
                _record_error(errors, ("aggregate", proxy_key.replace("_min", "_max")), f"must be {expected_max:.17g}")
        else:
            if aggregate.get(proxy_key) is not None:
                _record_warning(warnings, ("aggregate", proxy_key), "must be null when no compressive cells")

    aggregate_gap_rows = aggregate.get("gap_threshold_rows")
    if not isinstance(aggregate_gap_rows, list):
        _record_error(errors, ("aggregate", "gap_threshold_rows"), "must be a list")
        return

    expected_gap = _collect_gap_buckets(rows)
    for threshold, values in expected_gap.items():
        observed_entry = None
        for row in aggregate_gap_rows:
            if not isinstance(row, dict):
                continue
            observed_threshold = _coerce_finite_float(row.get("delta1_threshold"))
            if observed_threshold is None:
                continue
            observed_key = _threshold_key(observed_threshold)
            if observed_key is None:
                continue
            if observed_key == threshold:
                observed_entry = row
                break
        if observed_entry is None:
            _record_warning(warnings, ("aggregate", "gap_threshold_rows"), f"missing threshold {threshold}")
            continue

        observed_cell_count = _coerce_nonnegative_int(observed_entry.get("cell_count")) or 0
        if observed_cell_count != int(values["cell_count"]):
            _record_error(
                errors,
                ("aggregate", "gap_threshold_rows", threshold, "cell_count"),
                f"must be {int(values['cell_count'])!r}",
            )

        for key in ("p12_abs_sum", "p13_abs_sum", "p23_abs_sum", "p12_scaled_sum", "p13_scaled_sum", "p23_scaled_sum"):
            observed = _coerce_finite_float(observed_entry.get(key))
            expected = float(values.get(key, 0.0))
            if observed is None or abs(observed - expected) > TOLERANCE:
                _record_error(
                    errors,
                    ("aggregate", "gap_threshold_rows", threshold, key),
                    f"must be {expected:.17g}, got {observed!r}",
                )
        for key in ("p12_scaled_ge_one_count", "p13_scaled_ge_one_count", "p23_scaled_ge_one_count"):
            observed = _coerce_nonnegative_int(observed_entry.get(key)) or 0
            if observed != int(values.get(key, 0)):
                _record_error(errors, ("aggregate", "gap_threshold_rows", threshold, key), f"must be {int(values[key])!r}")

        if observed_cell_count > 0:
            for key, expected_key in (
                ("p12_abs_min", "p12_abs_min"),
                ("p13_abs_min", "p13_abs_min"),
                ("p23_abs_min", "p23_abs_min"),
                ("p12_scaled_min", "p12_scaled_min"),
                ("p13_scaled_min", "p13_scaled_min"),
                ("p23_scaled_min", "p23_scaled_min"),
                ("p12_abs_max", "p12_abs_max"),
                ("p13_abs_max", "p13_abs_max"),
                ("p23_abs_max", "p23_abs_max"),
                ("p12_scaled_max", "p12_scaled_max"),
                ("p13_scaled_max", "p13_scaled_max"),
                ("p23_scaled_max", "p23_scaled_max"),
            ):
                expected = values.get(expected_key)
                observed = _coerce_finite_float(observed_entry.get(key))
                if observed is None and expected is not None:
                    _record_error(errors, ("aggregate", "gap_threshold_rows", threshold, key), f"must be {expected:.17g}")
                elif expected is not None and observed is not None and abs(observed - expected) > TOLERANCE:
                    _record_error(errors, ("aggregate", "gap_threshold_rows", threshold, key), f"must be {expected:.17g}")
            if (
                _coerce_finite_float(observed_entry.get("p12_abs_min")) is not None
                and _coerce_finite_float(observed_entry.get("p12_abs_max")) is not None
                and _coerce_finite_float(observed_entry.get("p12_abs_min")) > _coerce_finite_float(observed_entry.get("p12_abs_max"))
            ):
                _record_error(errors, ("aggregate", "gap_threshold_rows", threshold), "p12_abs_min cannot exceed p12_abs_max")

            for proxy in ("p12", "p13", "p23"):
                row_sum = _coerce_finite_float(observed_entry.get(f"{proxy}_scaled_sum"))
                row_mean = _coerce_finite_float(observed_entry.get(f"{proxy}_scaled_mean"))
                if row_sum is None or row_mean is None:
                    _record_error(errors, ("aggregate", "gap_threshold_rows", threshold, f"{proxy}_scaled_mean"), "must be finite")
                elif abs(row_mean - (row_sum / float(observed_cell_count))) > TOLERANCE:
                    _record_error(
                        errors,
                        ("aggregate", "gap_threshold_rows", threshold, f"{proxy}_scaled_mean"),
                        f"must equal {row_sum / float(observed_cell_count):.17g}, got {row_mean:.17g}",
                    )
                row_sum = _coerce_finite_float(observed_entry.get(f"{proxy}_abs_sum"))
                row_mean = _coerce_finite_float(observed_entry.get(f"{proxy}_abs_mean"))
                if row_sum is None or row_mean is None:
                    _record_error(errors, ("aggregate", "gap_threshold_rows", threshold, f"{proxy}_abs_mean"), "must be finite")
                elif abs(row_mean - (row_sum / float(observed_cell_count))) > TOLERANCE:
                    _record_error(
                        errors,
                        ("aggregate", "gap_threshold_rows", threshold, f"{proxy}_abs_mean"),
                        f"must equal {row_sum / float(observed_cell_count):.17g}, got {row_mean:.17g}",
                    )
        else:
            for proxy in ("p12", "p13", "p23"):
                if observed_entry.get(f"{proxy}_abs_sum") not in (None, 0, 0.0):
                    _record_warning(warnings, ("aggregate", "gap_threshold_rows", threshold, f"{proxy}_abs_sum"), "expected 0.0 when no cells")
                if observed_entry.get(f"{proxy}_scaled_sum") not in (None, 0, 0.0):
                    _record_warning(warnings, ("aggregate", "gap_threshold_rows", threshold, f"{proxy}_scaled_sum"), "expected 0.0 when no cells")

        zone_fraction = _coerce_finite_float(observed_entry.get("zone_fraction"))
        expected_zone_fraction = _fraction(int(values["cell_count"]), expected_compressive)
        if zone_fraction is None:
            _record_error(errors, ("aggregate", "gap_threshold_rows", threshold, "zone_fraction"), "must be finite")
        elif abs(zone_fraction - expected_zone_fraction) > TOLERANCE:
            _record_error(
                errors,
                ("aggregate", "gap_threshold_rows", threshold, "zone_fraction"),
                f"must be {expected_zone_fraction:.17g}, got {zone_fraction:.17g}",
            )

    curve = aggregate.get("scaled_ge_one_threshold_curve")
    if not isinstance(curve, list):
        _record_warning(warnings, ("aggregate", "scaled_ge_one_threshold_curve"), "must be a list")
    else:
        curve_map = {
            _coerce_finite_float(item.get("delta1_threshold")): item
            for item in curve
            if isinstance(item, dict) and _coerce_finite_float(item.get("delta1_threshold")) is not None
        }
        for threshold, row in curve_map.items():
            key = _threshold_key(threshold)
            if key is None:
                continue
            match = None
            for candidate in aggregate_gap_rows:
                if not isinstance(candidate, dict):
                    continue
                candidate_threshold = _threshold_key(candidate.get("delta1_threshold"))
                if candidate_threshold is not None and candidate_threshold == key:
                    match = candidate
                    break
            if match is None:
                _record_warning(warnings, ("aggregate", "scaled_ge_one_threshold_curve"), f"unlinked threshold {threshold}")
                continue
            for key_name in (
                "p12_scaled_ge_one_fraction",
                "p13_scaled_ge_one_fraction",
                "p23_scaled_ge_one_fraction",
                "zone_fraction",
            ):
                observed = _coerce_finite_float(item := row.get(key_name))
                expected = _coerce_finite_float(match.get(key_name))
                if observed is None or expected is None:
                    continue
                if abs(observed - expected) > TOLERANCE:
                    _record_error(
                        errors,
                        ("aggregate", "scaled_ge_one_threshold_curve", key, key_name),
                        f"must match gap row {expected:.17g}, got {observed:.17g}",
                    )


def _validate_payload(payload: dict[str, Any]) -> tuple[list[str], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []

    _check_control_card(payload, errors)
    _check_contract(payload, errors)
    _check_route(payload, errors)
    _check_status(payload, errors)
    _check_authority(payload, errors)

    thresholds = _check_inputs(payload, warnings, errors)

    frames = payload.get("frames")
    if not isinstance(frames, list):
        _record_error(errors, ("frames",), "must be a list")
        frames = []

    row_summaries: list[dict[str, Any]] = []
    for index, row in enumerate(frames):
        if not isinstance(row, dict):
            _record_error(errors, ("frames", index), "must be an object")
            continue
        row_summaries.append(_validate_frame_row(row, index, thresholds, warnings, errors))

    _validate_aggregate(payload, frames, warnings, errors)

    if errors:
        return sorted(set(errors)), sorted(set(warnings))

    observed_status = payload.get("status")
    row_statuses = {entry.get("status") for entry in row_summaries} if row_summaries else {MISSING_REQUIRED_STATUS}
    expected_status = ERROR_STATUS
    if ERROR_STATUS in row_statuses:
        expected_status = ERROR_STATUS
    elif MISSING_REQUIRED_STATUS in row_statuses:
        expected_status = MISSING_REQUIRED_STATUS
    elif PARTIAL_STATUS in row_statuses:
        expected_status = PARTIAL_STATUS
    elif all(value == OK_STATUS for value in row_statuses):
        scan_warnings = payload.get("warnings")
        if isinstance(scan_warnings, list) and any(not _is_benign_warning(item) for item in scan_warnings):
            expected_status = PARTIAL_STATUS
        else:
            expected_status = OK_STATUS

    if observed_status in ALLOWED_STATUSES and observed_status != expected_status:
        _record_error(errors, ("status",), f"expected {expected_status!r}, got {observed_status!r}")

    return sorted(set(errors)), sorted(set(warnings))


def main() -> int:
    args = _parse_args()
    try:
        payload = _load_json(args.scan_json)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        result = {
            "contract": CONTRACT,
            "status": ERROR_STATUS,
            "scan_json": str(args.scan_json),
            "errors": [str(exc)],
            "warnings": [],
            "inputs": {"scan_json": str(args.scan_json), "output_json": str(args.output_json)},
            "route_decision": CHECK_ROUTE_DECISION,
            "changed_files": [str(args.scan_json), str(args.output_json)],
            "details": {
                "row_count": 0,
                "warn_count": 0,
                "error_count": 1,
                "status_counts": {"ok_frames": 0, "partial_frames": 0, "missing_frames": 0, "error_frames": 0},
            },
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
        }
        _write_json(args.output_json, result, args.pretty)
        print(json.dumps(result, sort_keys=True, indent=2 if args.pretty else None, allow_nan=False))
        return 1

    errors, warnings = _validate_payload(payload)
    status = ERROR_STATUS if errors else OK_STATUS
    row_count = len(payload.get("frames", []) if isinstance(payload.get("frames"), list) else [])
    frame_data = payload.get("frames", [])
    status_counts = {
        "ok_frames": 0,
        "partial_frames": 0,
        "missing_frames": 0,
        "error_frames": 0,
    }
    for row in frame_data if isinstance(frame_data, list) else []:
        if not isinstance(row, dict):
            status_counts["error_frames"] += 1
            continue
        if row.get("status") == OK_STATUS:
            status_counts["ok_frames"] += 1
        elif row.get("status") == PARTIAL_STATUS:
            status_counts["partial_frames"] += 1
        elif row.get("status") == MISSING_REQUIRED_STATUS:
            status_counts["missing_frames"] += 1
        else:
            status_counts["error_frames"] += 1

    result = {
        "contract": CONTRACT,
        "status": status,
        "scan_json": str(args.scan_json),
        "errors": errors,
        "warnings": warnings,
        "inputs": {"scan_json": str(args.scan_json), "output_json": str(args.output_json)},
        "route_decision": CHECK_ROUTE_DECISION,
        "changed_files": [str(args.scan_json), str(args.output_json)],
        "details": {
            "row_count": row_count,
            "warn_count": len(warnings),
            "error_count": len(errors),
            "status_counts": status_counts,
        },
        "authority": payload.get("authority"),
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
    }
    _write_json(args.output_json, result, args.pretty)
    print(json.dumps(result, sort_keys=True, indent=2 if args.pretty else None, allow_nan=False))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
