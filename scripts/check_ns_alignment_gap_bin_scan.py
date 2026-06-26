#!/usr/bin/env python3
"""Validate ns_alignment_gap_bin_scan output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_alignment_gap_bin_scan.py"
CONTRACT = "check_ns_alignment_gap_bin_scan"
SCAN_CONTRACT = "ns_alignment_gap_bin_scan"
SCAN_ROUTE_DECISION = "FAIL_CLOSED_NS_ALIGNMENT_GAP_BIN_SCAN"
SCAN_CHECK_ROUTE = "FAIL_CLOSED_NS_ALIGNMENT_GAP_BIN_SCAN_CHECK"

DEFAULT_SCAN_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_alignment_gap_bin_scan_N128_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "check_ns_alignment_gap_bin_scan_N128_20260621.json"
)

CONTROL_CARD = {
    "O": "Validate compressive-gap vorticity alignment scan output.",
    "R": (
        "Validate raw reconstruction scan rows, gap-threshold rows, and aggregate tally "
        "reconciliation against declared threshold bins and arithmetic identities."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed checker: schema violations, arithmetic mismatches, or invariant failures are errors.",
    "L": "Load scan JSON, verify control card, per-frame/gap rows, and aggregate counters.",
    "P": SCAN_CHECK_ROUTE,
    "G": "Checker is empirical only and does not introduce theorem-level claims.",
    "F": "Any mismatched count/fraction or threshold aggregation is a hard error.",
}

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
MISSING_REQUIRED_STATUS = "missing_required_field"
ERROR_STATUS = "error"
ALLOWED_STATUSES = {OK_STATUS, PARTIAL_STATUS, MISSING_REQUIRED_STATUS, ERROR_STATUS}
TOLERANCE = 1.0e-12
CHECK_CARD_KEYS = ("O", "R", "C", "S", "L", "P", "G", "F")
BENIGN_WARNING_SUFFIXES = (
    "velocity_snapshots axis-1 channel layout detected",
    "velocity_snapshots trailing channel layout detected",
    "velocity_snapshots last-axis layout detected",
    "velocity fallback axis-1 channel layout detected",
    "velocity fallback trailing channel layout detected",
    "converted legacy (T,N,N,N,3) velocity layout to components",
    "domain_length unavailable; using fallback 6.283185307179586",
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--scan-json",
        type=Path,
        default=DEFAULT_SCAN_JSON,
        help="Path to ns_alignment_gap_bin_scan output JSON.",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT_JSON,
        help="Path to write check output JSON.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print output.")
    return parser.parse_args()


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
        dump_kwargs = {"indent": 2}
    else:
        dump_kwargs = {"separators": (",", ":")}
    path.write_text(
        json.dumps(payload, sort_keys=True, allow_nan=False, **dump_kwargs) + "\n",
        encoding="utf-8",
    )


def _join_path(parts: tuple[Any, ...]) -> str:
    if not parts:
        return ""
    pieces: list[str] = []
    for part in parts:
        if isinstance(part, int):
            if pieces:
                pieces[-1] += f"[{part}]"
            else:
                pieces.append(f"[{part}]")
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


def _coerce_finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _coerce_nonnegative_int(value: Any) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if isinstance(value, float) and value.is_integer():
        return int(value) if int(value) >= 0 else None
    return None


def _coerce_nonnegative_float(value: Any) -> float | None:
    parsed = _coerce_finite_float(value)
    if parsed is None or parsed < 0.0:
        return None
    return parsed


def _coerce_nonempty_str(value: Any) -> str | None:
    if not isinstance(value, str):
        return None
    text = value.strip()
    return text if text else None


def _coerce_bool(value: Any) -> bool | None:
    return value if isinstance(value, bool) else None


def _is_benign_warning(value: Any) -> bool:
    if not isinstance(value, str):
        return False
    return any(value.endswith(suffix) or value == suffix for suffix in BENIGN_WARNING_SUFFIXES)


def _check_control_card(payload: dict[str, Any], errors: list[str]) -> None:
    for key in CHECK_CARD_KEYS:
        if _coerce_nonempty_str(payload.get(key)) is None:
            _record_error(errors, (key,), "must be non-empty string")


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


def _check_inputs(payload: dict[str, Any], warnings: list[str], errors: list[str]) -> list[float]:
    inputs = payload.get("inputs")
    if not isinstance(inputs, dict):
        _record_error(errors, ("inputs",), "must be an object")
        return []

    raw_archive = inputs.get("raw_archive")
    if not isinstance(raw_archive, str) or not raw_archive.strip():
        _record_error(errors, ("inputs", "raw_archive"), "must be non-empty string")

    frame = inputs.get("frame")
    if frame is not None and _coerce_nonnegative_int(frame) is None:
        _record_error(errors, ("inputs", "frame"), "must be null or nonnegative int")

    frame_limit = inputs.get("frame_limit")
    if frame_limit is not None and _coerce_nonnegative_int(frame_limit) is None:
        _record_error(errors, ("inputs", "frame_limit"), "must be null or nonnegative int")

    zero_eps = inputs.get("zero_eps")
    if _coerce_nonnegative_float(zero_eps) is None:
        _record_error(errors, ("inputs", "zero_eps"), "must be finite nonnegative")

    thresholds = []
    raw_thresholds = inputs.get("delta1_thresholds")
    if not isinstance(raw_thresholds, list) or not raw_thresholds:
        _record_error(errors, ("inputs", "delta1_thresholds"), "must be a non-empty list")
        return []
    for index, value in enumerate(raw_thresholds):
        parsed = _coerce_nonnegative_float(value)
        if parsed is None:
            _record_error(errors, ("inputs", "delta1_thresholds", index), "must be finite nonnegative float")
        else:
            thresholds.append(float(parsed))
    thresholds = sorted(set(thresholds))
    if not thresholds:
        _record_error(errors, ("inputs", "delta1_thresholds"), "no valid threshold values")

    if inputs.get("selected_frames") is not None and not isinstance(inputs.get("selected_frames"), list):
        _record_warning(warnings, ("inputs", "selected_frames"), "must be a list of nonnegative int if present")
    elif isinstance(inputs.get("selected_frames"), list):
        for index, value in enumerate(inputs.get("selected_frames")):
            if _coerce_nonnegative_int(value) is None:
                _record_warning(warnings, ("inputs", "selected_frames", index), "frame index must be nonnegative int")

    raw_count = inputs.get("raw_bundle_frame_count")
    if raw_count is not None and _coerce_nonnegative_int(raw_count) is None:
        _record_warning(warnings, ("inputs", "raw_bundle_frame_count"), "must be nonnegative int if present")

    return thresholds


def _check_fraction(
    value: Any,
    numerator: int | None,
    denominator: int,
    error_path: tuple[Any, ...],
    warnings: list[str],
    errors: list[str],
) -> float | None:
    observed = _coerce_finite_float(value)
    if observed is None:
        _record_error(errors, error_path, "must be finite")
        return None
    if observed < 0.0 or observed > 1.0:
        _record_warning(warnings, error_path, "fraction outside [0, 1]")
    expected = (float(numerator) / float(denominator)) if denominator not in (0, None) else 0.0
    if abs(observed - expected) > TOLERANCE:
        _record_error(errors, error_path, f"expected {expected:.17g}, got {observed:.17g}")
    return observed


def _validate_frame_row(
    row: dict[str, Any],
    index: int,
    input_thresholds: list[float],
    warnings: list[str],
    errors: list[str],
) -> dict[str, Any]:
    status = row.get("status")
    if status not in ALLOWED_STATUSES:
        _record_error(errors, ("frames", index, "status"), "must be one of ok|partial|missing_required_field|error")
        status = ERROR_STATUS

    frame = _coerce_nonnegative_int(row.get("frame"))
    if frame is None:
        _record_error(errors, ("frames", index, "frame"), "must be nonnegative int")

    snapshot = _coerce_nonnegative_int(row.get("snapshot_index"))
    if snapshot is None:
        _record_error(errors, ("frames", index, "snapshot_index"), "must be nonnegative int")

    for key in ("source", "lambda2_source", "vorticity_source"):
        if _coerce_nonempty_str(row.get(key)) is None:
            _record_error(errors, ("frames", index, key), "must be non-empty string")

    if status == ERROR_STATUS:
        row_errors = row.get("errors")
        if not isinstance(row_errors, list) or not row_errors:
            _record_error(errors, ("frames", index, "errors"), "error rows must include a non-empty errors list")
        return {"status": status, "frame": frame, "snapshot": snapshot, "alignable_zone_cell_count": 0}

    if status == MISSING_REQUIRED_STATUS:
        row_errors = row.get("errors")
        if not isinstance(row_errors, list) or not row_errors:
            _record_error(errors, ("frames", index, "errors"), "missing-required rows should include a non-empty errors list")

    cell_count = _coerce_nonnegative_int(row.get("cell_count"))
    finite_cell_count = _coerce_nonnegative_int(row.get("finite_cell_count"))
    if cell_count is None:
        _record_error(errors, ("frames", index, "cell_count"), "must be nonnegative int")
    if finite_cell_count is None:
        _record_error(errors, ("frames", index, "finite_cell_count"), "must be nonnegative int")
    if isinstance(cell_count, int) and isinstance(finite_cell_count, int) and finite_cell_count > cell_count:
        _record_error(errors, ("frames", index), "finite_cell_count cannot exceed cell_count")

    l2_pos = _coerce_nonnegative_int(row.get("lambda2_positive_count"))
    l2_neg = _coerce_nonnegative_int(row.get("lambda2_negative_count"))
    l2_zero = _coerce_nonnegative_int(row.get("lambda2_zero_count"))
    for key, value in (("lambda2_positive_count", l2_pos), ("lambda2_negative_count", l2_neg), ("lambda2_zero_count", l2_zero)):
        if value is None:
            _record_error(errors, ("frames", index, key), "must be nonnegative int")
    if (
        isinstance(finite_cell_count, int)
        and l2_pos is not None
        and l2_neg is not None
        and l2_zero is not None
        and l2_pos + l2_neg + l2_zero != finite_cell_count
    ):
        _record_error(errors, ("frames", index), "lambda2 counts must sum to finite_cell_count")

    l2_pos_f = _coerce_finite_float(row.get("lambda2_positive_fraction"))
    l2_neg_f = _coerce_finite_float(row.get("lambda2_negative_fraction"))
    l2_zero_f = _coerce_finite_float(row.get("lambda2_zero_fraction"))
    for fraction_key, count in (
        ("lambda2_positive_fraction", l2_pos),
        ("lambda2_negative_fraction", l2_neg),
        ("lambda2_zero_fraction", l2_zero),
    ):
        _check_fraction(
            row.get(fraction_key),
            count,
            finite_cell_count or 0,
            ("frames", index, fraction_key),
            warnings,
            errors,
        )
    if l2_pos_f is None or l2_neg_f is None or l2_zero_f is None:
        pass
    else:
        if abs((l2_pos_f + l2_neg_f + l2_zero_f) - 1.0) > 10.0 * TOLERANCE and finite_cell_count not in (None, 0):
            _record_warning(warnings, ("frames", index), "lambda2 fractions do not sum exactly to 1")

    compressive_zone_count = _coerce_nonnegative_int(row.get("compressive_zone_cell_count"))
    if compressive_zone_count is None:
        _record_error(errors, ("frames", index, "compressive_zone_cell_count"), "must be nonnegative int")
    if (
        isinstance(compressive_zone_count, int)
        and isinstance(finite_cell_count, int)
        and compressive_zone_count > finite_cell_count
    ):
        _record_error(errors, ("frames", index), "compressive_zone_cell_count cannot exceed finite_cell_count")

    alignable_zone_count = _coerce_nonnegative_int(row.get("alignable_zone_cell_count"))
    if alignable_zone_count is None:
        _record_error(errors, ("frames", index, "alignable_zone_cell_count"), "must be nonnegative int")
    if (
        isinstance(alignable_zone_count, int)
        and isinstance(compressive_zone_count, int)
        and alignable_zone_count > compressive_zone_count
    ):
        _record_error(errors, ("frames", index), "alignable_zone_cell_count cannot exceed compressive_zone_cell_count")

    align_e1 = _coerce_nonnegative_int(row.get("align_e1_count"))
    align_e3 = _coerce_nonnegative_int(row.get("align_e3_count"))
    align_tie = _coerce_nonnegative_int(row.get("align_tie_count"))
    align_success = _coerce_nonnegative_int(row.get("align_rule_success_count"))
    align_mismatch = _coerce_nonnegative_int(row.get("align_rule_mismatch_count"))
    for key, value in (
        ("align_e1_count", align_e1),
        ("align_e3_count", align_e3),
        ("align_tie_count", align_tie),
        ("align_rule_success_count", align_success),
        ("align_rule_mismatch_count", align_mismatch),
    ):
        if value is None:
            _record_error(errors, ("frames", index, key), "must be nonnegative int")

    if (
        isinstance(alignable_zone_count, int)
        and align_e1 is not None
        and align_e3 is not None
        and align_tie is not None
        and align_e1 + align_e3 + align_tie != alignable_zone_count
    ):
        _record_error(errors, ("frames", index), "alignment counts must sum to alignable_zone_cell_count")
    if align_e1 is not None and align_e3 is not None and align_success is not None and align_e1 + align_e3 != align_success:
        _record_error(errors, ("frames", index), "align_rule_success_count must equal align_e1_count + align_e3_count")
    if align_tie is not None and align_mismatch is not None and align_tie != align_mismatch:
        _record_error(errors, ("frames", index), "align_rule_mismatch_count must equal align_tie_count")
    if (
        align_success is not None
        and align_mismatch is not None
        and alignable_zone_count is not None
        and align_success + align_mismatch != alignable_zone_count
    ):
        _record_error(errors, ("frames", index), "align_rule_success_count + align_rule_mismatch_count must equal alignable_zone_cell_count")

    for fraction_key, count_key in (
        ("align_e1_fraction", "align_e1_count"),
        ("align_e3_fraction", "align_e3_count"),
        ("align_tie_fraction", "align_tie_count"),
        ("align_rule_success_fraction", "align_rule_success_count"),
        ("align_rule_mismatch_fraction", "align_rule_mismatch_count"),
    ):
        count = row.get(count_key)
        _check_fraction(
            row.get(fraction_key),
            int(count) if isinstance(count, int) else None,
            alignable_zone_count or 0,
            ("frames", index, fraction_key),
            warnings,
            errors,
        )

    delta1_sum = _coerce_nonnegative_float(row.get("delta1_sum"))
    if delta1_sum is None:
        _record_error(errors, ("frames", index, "delta1_sum"), "must be finite nonnegative float")

    delta1_min = row.get("delta1_min")
    delta1_max = row.get("delta1_max")
    delta1_mean = _coerce_nonnegative_float(row.get("delta1_mean"))
    if delta1_mean is None:
        _record_error(errors, ("frames", index, "delta1_mean"), "must be finite nonnegative float")

    if alignable_zone_count not in (None, 0):
        if isinstance(alignable_zone_count, int) and alignable_zone_count > 0:
            delta1_min_f = _coerce_finite_float(delta1_min)
            delta1_max_f = _coerce_finite_float(delta1_max)
            if delta1_min_f is None:
                _record_error(errors, ("frames", index, "delta1_min"), "must be finite when alignable_zone_cell_count > 0")
            if delta1_max_f is None:
                _record_error(errors, ("frames", index, "delta1_max"), "must be finite when alignable_zone_cell_count > 0")
            if delta1_min_f is not None and delta1_max_f is not None and delta1_min_f > delta1_max_f:
                _record_error(errors, ("frames", index), "delta1_min must not exceed delta1_max")
            if delta1_sum is not None and abs((delta1_sum / float(alignable_zone_count)) - (delta1_mean or 0.0)) > TOLERANCE:
                _record_error(errors, ("frames", index), "delta1_mean must equal delta1_sum / alignable_zone_cell_count")
    else:
        if delta1_min is not None:
            _record_warning(warnings, ("frames", index, "delta1_min"), "delta1_min should remain null when no alignable cells")
        if delta1_max is not None:
            _record_warning(warnings, ("frames", index, "delta1_max"), "delta1_max should remain null when no alignable cells")

    threshold_rows = row.get("gap_threshold_rows")
    if not isinstance(threshold_rows, list):
        _record_error(errors, ("frames", index, "gap_threshold_rows"), "must be a list")
        return {"status": status, "frame": frame, "snapshot": snapshot, "alignable_zone_cell_count": alignable_zone_count or 0}

    declared = {float(value): 0 for value in input_thresholds}
    for threshold_index, threshold_row in enumerate(threshold_rows):
        if not isinstance(threshold_row, dict):
            _record_error(errors, ("frames", index, "gap_threshold_rows", threshold_index), "threshold row must be an object")
            continue
        threshold_raw = threshold_row.get("delta1_threshold")
        threshold = _coerce_finite_float(threshold_raw)
        if threshold is None or threshold < 0.0:
            _record_error(errors, ("frames", index, "gap_threshold_rows", threshold_index, "delta1_threshold"), "must be finite nonnegative")
            continue
        if threshold in declared:
            declared[threshold] += 1
        else:
            _record_warning(warnings, ("frames", index, "gap_threshold_rows", threshold_index), "undeclared threshold present")

        gap_count = _coerce_nonnegative_int(threshold_row.get("cell_count"))
        if gap_count is None:
            _record_error(errors, ("frames", index, "gap_threshold_rows", threshold_index, "cell_count"), "must be nonnegative int")
            gap_count = 0

        if (
            isinstance(alignable_zone_count, int)
            and gap_count is not None
            and gap_count > alignable_zone_count
        ):
            _record_error(
                errors,
                ("frames", index, "gap_threshold_rows", threshold_index, "cell_count"),
                "gap threshold cell_count cannot exceed alignable_zone_cell_count",
            )

        gap_e1 = _coerce_nonnegative_int(threshold_row.get("align_e1_count"))
        gap_e3 = _coerce_nonnegative_int(threshold_row.get("align_e3_count"))
        gap_tie = _coerce_nonnegative_int(threshold_row.get("align_tie_count"))
        gap_success = _coerce_nonnegative_int(threshold_row.get("align_success_count"))
        gap_mismatch = _coerce_nonnegative_int(threshold_row.get("align_mismatch_count"))
        for key, value in (
            ("align_e1_count", gap_e1),
            ("align_e3_count", gap_e3),
            ("align_tie_count", gap_tie),
            ("align_success_count", gap_success),
            ("align_mismatch_count", gap_mismatch),
        ):
            if value is None:
                _record_error(errors, ("frames", index, "gap_threshold_rows", threshold_index, key), "must be nonnegative int")

        if gap_e1 is not None and gap_e3 is not None and gap_tie is not None and gap_e1 + gap_e3 + gap_tie != gap_count:
            _record_error(
                errors,
                ("frames", index, "gap_threshold_rows", threshold_index),
                "gap counts must sum to gap cell_count",
            )
        if gap_success is not None and gap_mismatch is not None and gap_success + gap_mismatch != gap_count:
            _record_error(
                errors,
                ("frames", index, "gap_threshold_rows", threshold_index),
                "gap success/mismatch counts must sum to gap cell_count",
            )
        if gap_e1 is not None and gap_e3 is not None and gap_success is not None and gap_success != gap_e1 + gap_e3:
            _record_error(
                errors,
                ("frames", index, "gap_threshold_rows", threshold_index),
                "gap align_success_count must equal gap_e1_count + gap_e3_count",
            )
        if gap_tie is not None and gap_mismatch is not None and gap_tie != gap_mismatch:
            _record_error(
                errors,
                ("frames", index, "gap_threshold_rows", threshold_index),
                "gap align_mismatch_count must equal gap_tie_count",
            )

        for fraction_key, count_key in (
            ("align_e1_fraction", gap_e1),
            ("align_e3_fraction", gap_e3),
            ("align_tie_fraction", gap_tie),
            ("align_success_fraction", gap_success),
            ("align_mismatch_fraction", gap_mismatch),
        ):
            _check_fraction(
                threshold_row.get(f"{fraction_key}"),
                int(count_key) if isinstance(count_key, int) else None,
                gap_count,
                ("frames", index, "gap_threshold_rows", threshold_index, fraction_key),
                warnings,
                errors,
            )

        zone_fraction = _coerce_finite_float(threshold_row.get("align_zone_fraction"))
        if zone_fraction is None:
            _record_error(errors, ("frames", index, "gap_threshold_rows", threshold_index, "align_zone_fraction"), "must be finite")
        elif alignable_zone_count not in (None, 0):
            expected_zone_fraction = gap_count / float(alignable_zone_count) if alignable_zone_count > 0 else 0.0
            if abs(zone_fraction - expected_zone_fraction) > TOLERANCE:
                _record_error(
                    errors,
                    ("frames", index, "gap_threshold_rows", threshold_index, "align_zone_fraction"),
                    f"expected {expected_zone_fraction:.17g}, got {zone_fraction:.17g}",
                )

    for threshold, count in declared.items():
        if count == 0:
            _record_warning(warnings, ("frames", index, "gap_threshold_rows"), f"missing declared threshold {threshold}")
        if count > 1:
            _record_warning(warnings, ("frames", index, "gap_threshold_rows"), f"duplicate threshold {threshold}")

    return {
        "status": status,
        "frame": frame,
        "snapshot": snapshot,
        "alignable_zone_cell_count": alignable_zone_count or 0,
    }


def _validate_frames(
    payload: dict[str, Any],
    input_thresholds: list[float],
    warnings: list[str],
    errors: list[str],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], dict[str, int]]:
    rows_value = payload.get("frames")
    if not isinstance(rows_value, list):
        _record_error(errors, ("frames",), "must be a list")
        return [], [], {"ok_frames": 0, "partial_frames": 0, "missing_frames": 0, "error_frames": 0}

    status_counts = {"ok_frames": 0, "partial_frames": 0, "missing_frames": 0, "error_frames": 0}
    valid_rows: list[dict[str, Any]] = []
    row_meta: list[dict[str, Any]] = []
    for index, row in enumerate(rows_value):
        if not isinstance(row, dict):
            _record_error(errors, ("frames", index), "must be an object")
            status_counts["error_frames"] += 1
            continue
        meta = _validate_frame_row(row, index, input_thresholds, warnings, errors)
        row_meta.append(meta)
        status = meta.get("status")
        if status == OK_STATUS:
            status_counts["ok_frames"] += 1
        elif status == PARTIAL_STATUS:
            status_counts["partial_frames"] += 1
        elif status == MISSING_REQUIRED_STATUS:
            status_counts["missing_frames"] += 1
        else:
            status_counts["error_frames"] += 1
        if status in ALLOWED_STATUSES and status != ERROR_STATUS:
            valid_rows.append(row)
    return rows_value, row_meta, status_counts


def _coerce_threshold_rows_for_check(threshold_rows: list[dict[str, Any]]) -> dict[float, dict[str, float | int]]:
    result: dict[float, dict[str, float | int]] = {}
    for row in threshold_rows:
        if not isinstance(row, dict):
            continue
        threshold = _coerce_finite_float(row.get("delta1_threshold"))
        if threshold is None or threshold < 0.0:
            continue
        key = float(threshold)
        accumulator = result.setdefault(
            key,
            {
                "cell_count": 0,
                "align_e1_count": 0,
                "align_e3_count": 0,
                "align_tie_count": 0,
                "align_success_count": 0,
                "align_mismatch_count": 0,
            },
        )
        accumulator["cell_count"] += int(row.get("cell_count", 0))
        accumulator["align_e1_count"] += int(row.get("align_e1_count", 0))
        accumulator["align_e3_count"] += int(row.get("align_e3_count", 0))
        accumulator["align_tie_count"] += int(row.get("align_tie_count", 0))
        accumulator["align_success_count"] += int(row.get("align_success_count", 0))
        accumulator["align_mismatch_count"] += int(row.get("align_mismatch_count", 0))
    return result


def _validate_aggregate(
    payload: dict[str, Any],
    rows: list[Any],
    status_counts: dict[str, int],
    input_thresholds: list[float],
    warnings: list[str],
    errors: list[str],
) -> dict[str, Any]:
    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        _record_error(errors, ("aggregate",), "must be an object")
        return {}

    if aggregate.get("processed_frames") != len(rows):
        _record_error(errors, ("aggregate", "processed_frames"), f"expected {len(rows)!r}")
    for key in ("ok_frames", "partial_frames", "missing_frames", "error_frames"):
        if aggregate.get(key) != status_counts[key]:
            _record_error(errors, ("aggregate", key), f"must equal row status count {status_counts[key]!r}")

    expected_counts: dict[str, int] = {
        "global_lambda2_positive_count": 0,
        "global_lambda2_negative_count": 0,
        "global_lambda2_zero_count": 0,
        "global_compressive_zone_cell_count": 0,
        "global_alignable_zone_cell_count": 0,
        "global_align_e1_count": 0,
        "global_align_e3_count": 0,
        "global_align_tie_count": 0,
        "global_align_rule_success_count": 0,
        "global_align_rule_mismatch_count": 0,
    }
    expected_cell_count = 0
    expected_finite = 0
    expected_delta1_sum = 0.0
    for row in rows:
        if not isinstance(row, dict):
            continue
        expected_cell_count += int(row.get("cell_count", 0))
        expected_finite += int(row.get("finite_cell_count", 0))
        for row_key, agg_key in (
            ("lambda2_positive_count", "global_lambda2_positive_count"),
            ("lambda2_negative_count", "global_lambda2_negative_count"),
            ("lambda2_zero_count", "global_lambda2_zero_count"),
            ("compressive_zone_cell_count", "global_compressive_zone_cell_count"),
            ("alignable_zone_cell_count", "global_alignable_zone_cell_count"),
            ("align_e1_count", "global_align_e1_count"),
            ("align_e3_count", "global_align_e3_count"),
            ("align_tie_count", "global_align_tie_count"),
            ("align_rule_success_count", "global_align_rule_success_count"),
            ("align_rule_mismatch_count", "global_align_rule_mismatch_count"),
        ):
            expected_counts[agg_key] += int(row.get(row_key, 0))
        expected_delta1_sum += float(row.get("delta1_sum", 0.0))

    if aggregate.get("global_cell_count") != expected_cell_count:
        _record_error(errors, ("aggregate", "global_cell_count"), f"must be {expected_cell_count!r}")
    if aggregate.get("global_finite_cell_count") != expected_finite:
        _record_error(errors, ("aggregate", "global_finite_cell_count"), f"must be {expected_finite!r}")
    for key, expected in expected_counts.items():
        if aggregate.get(key) != expected:
            _record_error(errors, ("aggregate", key), f"must be {expected!r}")

    if aggregate.get("global_align_e1_count", 0) + aggregate.get("global_align_e3_count", 0) + aggregate.get("global_align_tie_count", 0) != int(
        aggregate.get("global_alignable_zone_cell_count", 0)
    ):
        _record_error(
            errors,
            ("aggregate",),
            "global alignment counts must sum to global_alignable_zone_cell_count",
        )
    if aggregate.get("global_align_rule_success_count", 0) + aggregate.get("global_align_rule_mismatch_count", 0) != int(
        aggregate.get("global_alignable_zone_cell_count", 0)
    ):
        _record_error(
            errors,
            ("aggregate",),
            "global rule success/mismatch counts must sum to global_alignable_zone_cell_count",
        )
    if aggregate.get("global_align_rule_success_count", 0) != aggregate.get("global_align_e1_count", 0) + aggregate.get("global_align_e3_count", 0):
        _record_error(
            errors,
            ("aggregate",),
            "global_align_rule_success_count must equal global_align_e1_count + global_align_e3_count",
        )
    if aggregate.get("global_align_rule_mismatch_count", 0) != aggregate.get("global_align_tie_count", 0):
        _record_error(errors, ("aggregate",), "global_align_rule_mismatch_count must equal global_align_tie_count")

    align_region = int(aggregate.get("global_alignable_zone_cell_count", 0))
    finite_region = int(aggregate.get("global_finite_cell_count", 0))
    for numerator_key, denominator, fraction_key in (
        ("global_lambda2_positive_count", "global_finite_cell_count", "global_lambda2_positive_fraction"),
        ("global_lambda2_negative_count", "global_finite_cell_count", "global_lambda2_negative_fraction"),
        ("global_lambda2_zero_count", "global_finite_cell_count", "global_lambda2_zero_fraction"),
        ("global_align_e1_count", "global_alignable_zone_cell_count", "global_align_e1_fraction"),
        ("global_align_e3_count", "global_alignable_zone_cell_count", "global_align_e3_fraction"),
        ("global_align_tie_count", "global_alignable_zone_cell_count", "global_align_tie_fraction"),
        ("global_align_rule_success_count", "global_alignable_zone_cell_count", "global_align_rule_success_fraction"),
        ("global_align_rule_mismatch_count", "global_alignable_zone_cell_count", "global_align_rule_mismatch_fraction"),
    ):
        num = _coerce_nonnegative_int(aggregate.get(numerator_key)) or 0
        if denominator == "global_finite_cell_count":
            den = finite_region
        else:
            den = align_region
        expected = _fraction(num, den)
        observed = _coerce_finite_float(aggregate.get(fraction_key))
        if observed is None:
            _record_error(errors, ("aggregate", fraction_key), "must be finite")
            continue
        if abs(observed - expected) > TOLERANCE:
            _record_error(errors, ("aggregate", fraction_key), f"expected {expected:.17g}, got {observed:.17g}")

    aggregate_delta1_sum = _coerce_finite_float(aggregate.get("global_delta1_sum"))
    if aggregate_delta1_sum is None:
        _record_error(errors, ("aggregate", "global_delta1_sum"), "must be finite")
    else:
        if abs(aggregate_delta1_sum - expected_delta1_sum) > TOLERANCE:
            _record_error(
                errors,
                ("aggregate", "global_delta1_sum"),
                f"expected {expected_delta1_sum:.17g}, got {aggregate_delta1_sum:.17g}",
            )

    aggregate_delta1_min = aggregate.get("global_delta1_min")
    aggregate_delta1_max = aggregate.get("global_delta1_max")
    if align_region > 0:
        if _coerce_finite_float(aggregate_delta1_min) is None:
            _record_error(errors, ("aggregate", "global_delta1_min"), "must be finite when alignable zone is non-empty")
        if _coerce_finite_float(aggregate_delta1_max) is None:
            _record_error(errors, ("aggregate", "global_delta1_max"), "must be finite when alignable zone is non-empty")
        if _coerce_finite_float(aggregate_delta1_min) is not None and _coerce_finite_float(aggregate_delta1_max) is not None:
            if float(aggregate_delta1_min) > float(aggregate_delta1_max):
                _record_error(errors, ("aggregate",), "global_delta1_min must not exceed global_delta1_max")
    else:
        if aggregate_delta1_min is not None:
            _record_warning(warnings, ("aggregate", "global_delta1_min"), "should be null when no alignable zone cells")
        if aggregate_delta1_max is not None:
            _record_warning(warnings, ("aggregate", "global_delta1_max"), "should be null when no alignable zone cells")

    aggregate_delta1_mean = _coerce_nonnegative_float(aggregate.get("global_delta1_mean"))
    if aggregate_delta1_mean is None:
        _record_error(errors, ("aggregate", "global_delta1_mean"), "must be finite nonnegative")
    elif align_region > 0 and aggregate_delta1_sum is not None and abs(aggregate_delta1_mean - (aggregate_delta1_sum / float(align_region))) > TOLERANCE:
        _record_error(errors, ("aggregate", "global_delta1_mean"), "must equal global_delta1_sum / global_alignable_zone_cell_count")
    elif align_region == 0 and aggregate_delta1_mean != 0.0:
        _record_error(errors, ("aggregate", "global_delta1_mean"), "must be 0.0 when no alignable zone cells")

    aggregate_gap_rows = aggregate.get("gap_threshold_rows")
    if not isinstance(aggregate_gap_rows, list):
        _record_error(errors, ("aggregate", "gap_threshold_rows"), "must be a list")
        return aggregate

    threshold_rows_to_accumulate: list[dict[str, Any]] = []
    for row in rows:
        if not isinstance(row, dict):
            continue
        row_gap_rows = row.get("gap_threshold_rows")
        if isinstance(row_gap_rows, list):
            threshold_rows_to_accumulate.extend(entry for entry in row_gap_rows if isinstance(entry, dict))
    expected_gap_map = _coerce_threshold_rows_for_check(threshold_rows_to_accumulate)
    seen_thresholds = {float(key) for key in expected_gap_map.keys()}
    for threshold in input_thresholds:
        if threshold not in seen_thresholds:
            _record_warning(warnings, ("aggregate", "gap_threshold_rows"), f"declared threshold {threshold} missing from aggregate rows")

    for entry in aggregate_gap_rows:
        if not isinstance(entry, dict):
            _record_error(errors, ("aggregate", "gap_threshold_rows"), "entries must be objects")
            continue
        threshold = _coerce_finite_float(entry.get("delta1_threshold"))
        if threshold is None or threshold < 0.0:
            _record_error(errors, ("aggregate", "gap_threshold_rows"), "entry threshold must be finite nonnegative")
            continue
        key = float(threshold)
        expected = expected_gap_map.get(key)
        if expected is None:
            _record_warning(warnings, ("aggregate", "gap_threshold_rows"), f"threshold {key} missing in frame accumulation")
            expected = {
                "cell_count": 0,
                "align_e1_count": 0,
                "align_e3_count": 0,
                "align_tie_count": 0,
                "align_success_count": 0,
                "align_mismatch_count": 0,
            }

        cell_count = _coerce_nonnegative_int(entry.get("cell_count"))
        align_e1 = _coerce_nonnegative_int(entry.get("align_e1_count"))
        align_e3 = _coerce_nonnegative_int(entry.get("align_e3_count"))
        align_tie = _coerce_nonnegative_int(entry.get("align_tie_count"))
        align_success = _coerce_nonnegative_int(entry.get("align_success_count"))
        align_mismatch = _coerce_nonnegative_int(entry.get("align_mismatch_count"))
        if cell_count is None:
            _record_error(errors, ("aggregate", "gap_threshold_rows", threshold, "cell_count"), "must be nonnegative int")
            cell_count = 0
        if align_e1 is None:
            _record_error(errors, ("aggregate", "gap_threshold_rows", threshold, "align_e1_count"), "must be nonnegative int")
            align_e1 = 0
        if align_e3 is None:
            _record_error(errors, ("aggregate", "gap_threshold_rows", threshold, "align_e3_count"), "must be nonnegative int")
            align_e3 = 0
        if align_tie is None:
            _record_error(errors, ("aggregate", "gap_threshold_rows", threshold, "align_tie_count"), "must be nonnegative int")
            align_tie = 0
        if align_success is None:
            _record_error(errors, ("aggregate", "gap_threshold_rows", threshold, "align_success_count"), "must be nonnegative int")
            align_success = 0
        if align_mismatch is None:
            _record_error(errors, ("aggregate", "gap_threshold_rows", threshold, "align_mismatch_count"), "must be nonnegative int")
            align_mismatch = 0

        if align_e1 + align_e3 + align_tie != cell_count:
            _record_error(errors, ("aggregate", "gap_threshold_rows", threshold), "threshold counts must sum to cell_count")
        if align_success + align_mismatch != cell_count:
            _record_error(errors, ("aggregate", "gap_threshold_rows", threshold), "threshold success+gap mismatch must sum to cell_count")
        if align_success != align_e1 + align_e3:
            _record_error(errors, ("aggregate", "gap_threshold_rows", threshold), "aggregate align_success_count must equal e1+e3")
        if align_tie != align_mismatch:
            _record_error(errors, ("aggregate", "gap_threshold_rows", threshold), "aggregate align_mismatch_count must equal tie_count")

        for key, observed, expected_value in (
            ("cell_count", cell_count, expected["cell_count"]),
            ("align_e1_count", align_e1, expected["align_e1_count"]),
            ("align_e3_count", align_e3, expected["align_e3_count"]),
            ("align_tie_count", align_tie, expected["align_tie_count"]),
            ("align_success_count", align_success, expected["align_success_count"]),
            ("align_mismatch_count", align_mismatch, expected["align_mismatch_count"]),
        ):
            if int(observed) != int(expected_value):
                _record_error(
                    errors,
                    ("aggregate", "gap_threshold_rows", threshold, key),
                    f"must match row accumulation {expected_value!r}",
                )

        if align_region > 0:
            expected_zone_fraction = _fraction(cell_count, align_region)
            aggregate_zone_fraction = _coerce_finite_float(entry.get("align_zone_fraction"))
            if aggregate_zone_fraction is None:
                _record_error(errors, ("aggregate", "gap_threshold_rows", threshold, "align_zone_fraction"), "must be finite")
            elif abs(aggregate_zone_fraction - expected_zone_fraction) > TOLERANCE:
                _record_error(
                    errors,
                    ("aggregate", "gap_threshold_rows", threshold, "align_zone_fraction"),
                    f"expected {expected_zone_fraction:.17g}, got {aggregate_zone_fraction:.17g}",
                )

        if cell_count:
            for fraction_key, expected_count in (
                ("align_e1_fraction", align_e1),
                ("align_e3_fraction", align_e3),
                ("align_tie_fraction", align_tie),
                ("align_success_fraction", align_success),
                ("align_mismatch_fraction", align_mismatch),
            ):
                observed_fraction = _coerce_finite_float(entry.get(fraction_key))
                if observed_fraction is None:
                    _record_error(errors, ("aggregate", "gap_threshold_rows", threshold, fraction_key), "must be finite")
                    continue
                expected_fraction = _fraction(int(expected_count), int(cell_count))
                if abs(observed_fraction - expected_fraction) > TOLERANCE:
                    _record_error(
                        errors,
                        ("aggregate", "gap_threshold_rows", threshold, fraction_key),
                        f"expected {expected_fraction:.17g}, got {observed_fraction:.17g}",
                    )
    curve = aggregate.get("gap_threshold_success_curve")
    if not isinstance(curve, list):
        _record_error(errors, ("aggregate", "gap_threshold_success_curve"), "must be a list")
        return aggregate
    curve_thresholds = {_coerce_finite_float(item.get("delta1_threshold")): item for item in curve if isinstance(item, dict)}
    for expected_threshold in input_thresholds:
        if expected_threshold not in curve_thresholds:
            _record_warning(warnings, ("aggregate", "gap_threshold_success_curve"), f"missing threshold {expected_threshold}")
    for item in curve:
        if not isinstance(item, dict):
            _record_error(errors, ("aggregate", "gap_threshold_success_curve"), "entry must be object")
            continue
        threshold = _coerce_finite_float(item.get("delta1_threshold"))
        if threshold is None or threshold < 0.0:
            _record_error(errors, ("aggregate", "gap_threshold_success_curve"), "delta1_threshold must be finite nonnegative")
            continue
        entry_threshold = aggregate.get("gap_threshold_rows")
        matching = None
        if isinstance(entry_threshold, list):
            for agg_row in entry_threshold:
                if not isinstance(agg_row, dict):
                    continue
                if _coerce_finite_float(agg_row.get("delta1_threshold")) == threshold:
                    matching = agg_row
                    break
        if matching is None:
            _record_warning(warnings, ("aggregate", "gap_threshold_success_curve"), f"unlinked threshold {threshold}")
            continue
        expected_success = _coerce_finite_float(matching.get("align_success_fraction"))
        expected_mismatch = _coerce_finite_float(matching.get("align_mismatch_fraction"))
        observed_success = _coerce_finite_float(item.get("success_fraction"))
        observed_mismatch = _coerce_finite_float(item.get("mismatch_fraction"))
        if expected_success is None or expected_mismatch is None:
            continue
        if observed_success is None:
            _record_error(errors, ("aggregate", "gap_threshold_success_curve", threshold, "success_fraction"), "must be finite")
        elif abs(observed_success - expected_success) > TOLERANCE:
            _record_error(
                errors,
                ("aggregate", "gap_threshold_success_curve", threshold, "success_fraction"),
                f"expected {expected_success:.17g}, got {observed_success:.17g}",
            )
        if observed_mismatch is None:
            _record_error(errors, ("aggregate", "gap_threshold_success_curve", threshold, "mismatch_fraction"), "must be finite")
        elif abs(observed_mismatch - expected_mismatch) > TOLERANCE:
            _record_error(
                errors,
                ("aggregate", "gap_threshold_success_curve", threshold, "mismatch_fraction"),
                f"expected {expected_mismatch:.17g}, got {observed_mismatch:.17g}",
            )
    return aggregate


def _fraction(numerator: int, denominator: int) -> float:
    if denominator <= 0:
        return 0.0
    return float(numerator) / float(denominator)


def _validate_payload(payload: dict[str, Any]) -> tuple[list[str], list[str], dict[str, Any]]:
    errors: list[str] = []
    warnings: list[str] = []

    if payload.get("contract") != SCAN_CONTRACT:
        _record_error(errors, ("contract",), f"must be {SCAN_CONTRACT!r}")
    if payload.get("route_decision") != SCAN_ROUTE_DECISION:
        _record_error(errors, ("route_decision",), f"must be {SCAN_ROUTE_DECISION!r}")

    status = payload.get("status")
    if status not in ALLOWED_STATUSES:
        _record_error(errors, ("status",), f"must be one of {sorted(ALLOWED_STATUSES)!r}")

    _check_control_card(payload, errors)
    _check_authority(payload, errors)
    input_thresholds = _check_inputs(payload, warnings, errors)

    rows, row_meta, status_counts = _validate_frames(payload, input_thresholds, warnings, errors)
    if rows:
        aggregate = _validate_aggregate(payload, rows, status_counts, input_thresholds, warnings, errors)
    else:
        aggregate = payload.get("aggregate")
        if not isinstance(aggregate, dict):
            _record_error(errors, ("aggregate",), "must be an object when no rows")

    if status in ALLOWED_STATUSES:
        observed_status = status
        statuses = {entry.get("status") for entry in row_meta} if row_meta else {MISSING_REQUIRED_STATUS}
        expected_status = ERROR_STATUS
        if ERROR_STATUS in statuses:
            expected_status = ERROR_STATUS
        elif MISSING_REQUIRED_STATUS in statuses:
            expected_status = MISSING_REQUIRED_STATUS
        elif PARTIAL_STATUS in statuses:
            expected_status = PARTIAL_STATUS
        elif statuses == {OK_STATUS}:
            scan_warnings = payload.get("warnings")
            expected_status = (
                PARTIAL_STATUS
                if isinstance(scan_warnings, list) and any(not _is_benign_warning(warning) for warning in scan_warnings)
                else OK_STATUS
            )
        elif statuses:
            expected_status = PARTIAL_STATUS
        if observed_status != expected_status:
            _record_error(errors, ("status",), f"expected {expected_status!r} from row statuses, got {observed_status!r}")

    details = {
        "status_counts": status_counts,
        "row_count": len(rows),
        "input_threshold_count": len(input_thresholds),
        "warn_count": len(warnings),
        "error_count": len(errors),
    }
    return errors, warnings, details


def main() -> int:
    args = _parse_args()
    try:
        payload = _load_json(args.scan_json)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        output_payload = {
            "contract": CONTRACT,
            "status": ERROR_STATUS,
            "scan_json": str(args.scan_json),
            "input_json": str(args.scan_json),
            "errors": [str(exc)],
            "warnings": [],
            "input": {"scan_json": str(args.scan_json), "output_json": str(args.output_json)},
            "changed_files": [str(args.scan_json), str(args.output_json)],
            "details": {"row_count": 0, "status_counts": {}, "input_threshold_count": 0},
            **CONTROL_CARD,
            "control_card": CONTROL_CARD,
        }
        _write_json(args.output_json, output_payload, args.pretty)
        print(json.dumps(output_payload, sort_keys=True, indent=2 if args.pretty else None, allow_nan=False))
        return 1

    errors, warnings, details = _validate_payload(payload)
    result = {
        "contract": CONTRACT,
        "status": ERROR_STATUS if errors else OK_STATUS,
        "scan_json": str(args.scan_json),
        "input_json": str(args.scan_json),
        "errors": errors,
        "warnings": warnings,
        "input": {"scan_json": str(args.scan_json), "output_json": str(args.output_json)},
        "changed_files": [str(args.scan_json), str(args.output_json)],
        "details": details,
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
    }
    _write_json(args.output_json, result, args.pretty)
    print(json.dumps(result, sort_keys=True, indent=2 if args.pretty else None, allow_nan=False))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
