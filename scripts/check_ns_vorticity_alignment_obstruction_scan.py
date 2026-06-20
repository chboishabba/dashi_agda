#!/usr/bin/env python3
"""Validate the compressive/ extensional vorticity alignment obstruction scan contract."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_vorticity_alignment_obstruction_scan.py"
CONTRACT = "check_ns_vorticity_alignment_obstruction_scan"
SCAN_CONTRACT = "ns_vorticity_alignment_obstruction_scan"
SCAN_ROUTE_DECISION = "FAIL_CLOSED_NS_VORTICITY_ALIGNMENT_OBSTRUCTION_SCAN"
SCAN_CHECK_ROUTE = "FAIL_CLOSED_NS_VORTICITY_ALIGNMENT_OBSTRUCTION_SCAN_CHECK"

DEFAULT_SCAN_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_vorticity_alignment_obstruction_scan_N128_20260621.json"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_vorticity_alignment_obstruction_scan_check_N128_20260621.json"
)

CHECK_CARD_KEYS = ("O", "R", "C", "S", "L", "P", "G", "F")
SCAN_REQUIRED_INPUT_KEYS = ("raw_archive", "frame", "frame_limit", "zero_eps", "selected_frames")

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
MISSING_REQUIRED_STATUS = "missing_required_field"
ERROR_STATUS = "error"
ALLOWED_SCAN_STATUS = {OK_STATUS, PARTIAL_STATUS, MISSING_REQUIRED_STATUS, ERROR_STATUS}

COUNT_KEYS = (
    "lambda2_positive_count",
    "lambda2_negative_count",
    "lambda2_zero_count",
    "lambda2_region_cell_count",
    "alignment_region_cell_count",
    "align_e1_count",
    "align_e3_count",
    "align_tie_count",
    "align_rule_success_count",
    "align_rule_mismatch_count",
)

FRACTION_KEYS = (
    ("lambda2_positive_fraction", "lambda2_positive_count"),
    ("lambda2_negative_fraction", "lambda2_negative_count"),
    ("lambda2_zero_fraction", "lambda2_zero_count"),
    ("align_e1_fraction", "align_e1_count"),
    ("align_e3_fraction", "align_e3_count"),
    ("align_tie_fraction", "align_tie_count"),
    ("align_rule_success_fraction", "align_rule_success_count"),
    ("align_rule_mismatch_fraction", "align_rule_mismatch_count"),
)

CONTROL_CARD = {
    "O": "Validate the compressive/ extensional vorticity alignment obstruction scan contract.",
    "R": (
        "Validate per-frame and aggregate counts/fractions, region coverage, alignment-tally consistency, "
        "and frame/aggregate telemetry arithmetic."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed checker: malformed schema, status mismatches, or arithmetic inconsistencies produce error.",
    "L": "Load scan JSON, validate schema, and report checker-level status.",
    "P": SCAN_CHECK_ROUTE,
    "G": "Checker is empirical only and does not infer any theorem or Clay claim.",
    "F": "Missing/invalid scan fields and failed schema checks are non-negotiable errors.",
}

LEGACY_AXIS_WARNING_SUFFIXES = (
    "velocity_snapshots axis-1 channel layout detected",
    "velocity_snapshots trailing channel layout detected",
    "velocity_snapshots last-axis channel layout detected",
    "velocity fallback axis-1 channel layout detected",
    "velocity fallback trailing channel layout detected",
    "converted legacy (T,N,N,N,3) velocity layout to components",
    "domain_length unavailable; using fallback",
)


def _is_benign_warning(value: str) -> bool:
    if not isinstance(value, str):
        return False
    return any(suffix in value for suffix in LEGACY_AXIS_WARNING_SUFFIXES)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scan-json", type=Path, default=DEFAULT_SCAN_JSON, help="Path to scan JSON")
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT, help="Checker output JSON path")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print output")
    return parser.parse_args()


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing input file: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"top-level payload must be an object: {path}")
    return payload


def _join_path(parts: tuple[Any, ...]) -> str:
    if not parts:
        return ""
    segments: list[str] = []
    for part in parts:
        if isinstance(part, int):
            if segments:
                segments[-1] = f"{segments[-1]}[{part}]"
            else:
                segments.append(f"[{part}]")
            continue
        if segments:
            segments.append(f".{part}")
        else:
            segments.append(str(part))
    return "".join(segments)


def _record_error(errors: list[str], path: tuple[Any, ...], message: str) -> None:
    label = _join_path(path)
    errors.append(f"{label}: {message}" if label else message)


def _record_warning(warnings: list[str], path: tuple[Any, ...], message: str) -> None:
    label = _join_path(path)
    warnings.append(f"{label}: {message}" if label else message)


def _coerce_finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, (int, float)):
        parsed = float(value)
    elif isinstance(value, str):
        try:
            parsed = float(value.strip())
        except ValueError:
            return None
    else:
        return None
    return parsed if math.isfinite(parsed) else None


def _coerce_nonnegative_int(value: Any) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if isinstance(value, float) and math.isfinite(value) and value.is_integer():
        parsed = int(value)
        return parsed if parsed >= 0 else None
    return None


def _coerce_nonempty_str(value: Any) -> str | None:
    if not isinstance(value, str):
        return None
    text = value.strip()
    return text if text else None


def _coerce_bool(value: Any) -> bool | None:
    return value if isinstance(value, bool) else None


def _coerce_nonnegative_int_list(value: Any) -> list[int] | None:
    if not isinstance(value, list):
        return None
    output: list[int] = []
    for item in value:
        if not isinstance(item, int) or item < 0:
            return None
        output.append(item)
    return output


def _check_control_card(payload: dict[str, Any], errors: list[str]) -> None:
    for key in CHECK_CARD_KEYS:
        if _coerce_nonempty_str(payload.get(key)) is None:
            _record_error(errors, (key,), "must be non-empty string")


def _check_contract(payload: dict[str, Any], errors: list[str]) -> None:
    if payload.get("contract") != SCAN_CONTRACT:
        _record_error(errors, ("contract",), f"must be {SCAN_CONTRACT!r}")


def _check_route(payload: dict[str, Any], errors: list[str]) -> None:
    route = payload.get("route_decision")
    if route is None:
        _record_error(errors, ("route_decision",), "missing route decision")
        return
    if route != SCAN_ROUTE_DECISION:
        _record_error(errors, ("route_decision",), f"must be {SCAN_ROUTE_DECISION!r}")


def _check_status(payload: dict[str, Any], errors: list[str]) -> None:
    status = payload.get("status")
    if status not in ALLOWED_SCAN_STATUS:
        _record_error(errors, ("status",), f"must be one of {sorted(ALLOWED_SCAN_STATUS)!r}")


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
        actual = authority.get(key)
        if _coerce_bool(actual) is None:
            _record_error(errors, ("authority", key), "must be bool")
            continue
        if actual is not expected_value:
            _record_error(errors, ("authority", key), f"must be {expected_value!r}")


def _check_inputs(payload: dict[str, Any], warnings: list[str], errors: list[str]) -> None:
    inputs = payload.get("inputs")
    if not isinstance(inputs, dict):
        _record_error(errors, ("inputs",), "must be an object")
        return
    for key in SCAN_REQUIRED_INPUT_KEYS:
        if key not in inputs:
            _record_warning(warnings, ("inputs",), f"missing optional metadata field {key!r}")

    raw_archive = inputs.get("raw_archive")
    if not isinstance(raw_archive, str) or not raw_archive.strip():
        _record_error(errors, ("inputs", "raw_archive"), "must be non-empty string")
    if inputs.get("frame") is not None and _coerce_nonnegative_int(inputs.get("frame")) is None:
        _record_error(errors, ("inputs", "frame"), "must be null or nonnegative int")
    if inputs.get("frame_limit") is not None and _coerce_nonnegative_int(inputs.get("frame_limit")) is None:
        _record_error(errors, ("inputs", "frame_limit"), "must be null or nonnegative int")
    eps = _coerce_finite_float(inputs.get("zero_eps"))
    if eps is None or eps < 0.0:
        _record_error(errors, ("inputs", "zero_eps"), "must be finite nonnegative")
    if _coerce_nonnegative_int_list(inputs.get("selected_frames")) is None:
        _record_warning(warnings, ("inputs", "selected_frames"), "must be list of nonnegative ints if present")


def _check_index_path(value: Any, path: tuple[Any, ...], errors: list[str]) -> None:
    if not isinstance(value, list) or len(value) != 3:
        _record_error(errors, path, "must be a 3-element index list")
        return
    for i, item in enumerate(value):
        if not isinstance(item, int) or item < 0:
            _record_error(errors, path + (i,), "must be nonnegative int")


def _validate_frame_row(row: dict[str, Any], index: int, errors: list[str], warnings: list[str]) -> None:
    status = row.get("status")
    if status not in ALLOWED_SCAN_STATUS:
        _record_error(errors, ("frames", index, "status"), f"invalid status {status!r}")

    frame = _coerce_nonnegative_int(row.get("frame"))
    if frame is None:
        _record_error(errors, ("frames", index, "frame"), "must be nonnegative int")
    snapshot = _coerce_nonnegative_int(row.get("snapshot_index"))
    if snapshot is None:
        _record_error(errors, ("frames", index, "snapshot_index"), "must be nonnegative int")
    source = _coerce_nonempty_str(row.get("source"))
    if source is None and status in {OK_STATUS, PARTIAL_STATUS, MISSING_REQUIRED_STATUS}:
        _record_error(errors, ("frames", index, "source"), "must be non-empty string")
    lambda2_source = _coerce_nonempty_str(row.get("lambda2_source"))
    if lambda2_source is None and status in {OK_STATUS, PARTIAL_STATUS, MISSING_REQUIRED_STATUS}:
        _record_error(errors, ("frames", index, "lambda2_source"), "must be non-empty string")
    vorticity_source = _coerce_nonempty_str(row.get("vorticity_source"))
    if vorticity_source is None and status in {OK_STATUS, PARTIAL_STATUS, MISSING_REQUIRED_STATUS}:
        _record_error(errors, ("frames", index, "vorticity_source"), "must be non-empty string")

    cell_count = _coerce_nonnegative_int(row.get("cell_count"))
    finite_count = _coerce_nonnegative_int(row.get("finite_cell_count"))
    l2_reg_count = _coerce_nonnegative_int(row.get("lambda2_region_cell_count"))
    align_region = _coerce_nonnegative_int(row.get("alignment_region_cell_count"))
    if status in {OK_STATUS, PARTIAL_STATUS, MISSING_REQUIRED_STATUS}:
        if cell_count is None:
            _record_error(errors, ("frames", index, "cell_count"), "must be nonnegative int")
        if finite_count is None:
            _record_error(errors, ("frames", index, "finite_cell_count"), "must be nonnegative int")
        if l2_reg_count is None:
            _record_error(errors, ("frames", index, "lambda2_region_cell_count"), "must be nonnegative int")
        if align_region is None:
            _record_error(errors, ("frames", index, "alignment_region_cell_count"), "must be nonnegative int")
        if isinstance(cell_count, int) and isinstance(finite_count, int) and finite_count > cell_count:
            _record_error(errors, ("frames", index), "finite_cell_count exceeds cell_count")
        if isinstance(finite_count, int) and isinstance(l2_reg_count, int) and l2_reg_count > finite_count:
            _record_error(errors, ("frames", index), "lambda2_region_cell_count exceeds finite_cell_count")
        if isinstance(align_region, int) and isinstance(l2_reg_count, int) and align_region > l2_reg_count:
            _record_error(errors, ("frames", index), "alignment_region_cell_count exceeds lambda2_region_cell_count")

        l2_pos = _coerce_nonnegative_int(row.get("lambda2_positive_count"))
        l2_neg = _coerce_nonnegative_int(row.get("lambda2_negative_count"))
        l2_zero = _coerce_nonnegative_int(row.get("lambda2_zero_count"))
        for key in COUNT_KEYS:
            if _coerce_nonnegative_int(row.get(key)) is None:
                _record_error(errors, ("frames", index, key), "must be nonnegative int")

        if (
            l2_pos is not None
            and l2_neg is not None
            and l2_zero is not None
            and finite_count is not None
            and l2_pos + l2_neg + l2_zero != finite_count
        ):
            _record_error(
                errors,
                ("frames", index),
                f"lambda2 counts must sum to finite_cell_count ({finite_count})",
            )

        align_e1 = _coerce_nonnegative_int(row.get("align_e1_count"))
        align_e3 = _coerce_nonnegative_int(row.get("align_e3_count"))
        align_tie = _coerce_nonnegative_int(row.get("align_tie_count"))
        align_rule_success = _coerce_nonnegative_int(row.get("align_rule_success_count"))
        align_rule_mismatch = _coerce_nonnegative_int(row.get("align_rule_mismatch_count"))
        if (
            align_e1 is not None
            and align_e3 is not None
            and align_tie is not None
            and align_region is not None
            and align_e1 + align_e3 + align_tie != align_region
        ):
            _record_error(
                errors,
                ("frames", index),
                f"align counts must sum to alignment_region_cell_count ({align_region})",
            )
        if (
            align_rule_success is not None
            and align_rule_mismatch is not None
            and align_region is not None
            and align_rule_success + align_rule_mismatch != align_region
        ):
            _record_error(
                errors,
                ("frames", index),
                "align_rule counts must sum to alignment_region_cell_count",
            )
        if (
            align_rule_success is not None
            and align_e1 is not None
            and align_e3 is not None
            and align_rule_success != align_e1 + align_e3
        ):
            _record_error(
                errors,
                ("frames", index),
                "align_rule_success_count must equal align_e1_count + align_e3_count",
            )
        if align_rule_mismatch is not None and align_tie is not None and align_rule_mismatch != align_tie:
            _record_error(errors, ("frames", index), "align_rule_mismatch_count must equal align_tie_count")

        for fraction_key, count_key in FRACTION_KEYS:
            fraction = _coerce_finite_float(row.get(fraction_key))
            count = _coerce_nonnegative_int(row.get(count_key))
            if fraction is None:
                _record_error(errors, ("frames", index, fraction_key), "must be finite")
                continue
            if fraction < 0.0 or fraction > 1.0:
                _record_warning(warnings, ("frames", index, fraction_key), "outside [0, 1]")
            denominator = align_region if count_key.startswith("align_") else finite_count
            expected = float(count) / float(denominator) if count is not None and denominator not in (None, 0) else 0.0
            if abs(fraction - expected) > 1.0e-12:
                _record_error(
                    errors,
                    ("frames", index, fraction_key),
                    f"expected {expected!r}, got {fraction!r}",
                )

        for key in ("align_e1_sq_sum", "align_e3_sq_sum", "align_e1_sq_min", "align_e1_sq_max", "align_e3_sq_min", "align_e3_sq_max"):
            if _coerce_finite_float(row.get(key)) is None and align_region not in (None, 0):
                _record_error(errors, ("frames", index, key), "must be finite for regions with nonzero cells")

        for key in ("align_e1_sq_mean", "align_e3_sq_mean", "align_e1_sq_min", "align_e1_sq_max", "align_e3_sq_min", "align_e3_sq_max"):
            value = _coerce_finite_float(row.get(key))
            if value is None and _coerce_nonnegative_int(row.get("alignment_region_cell_count"),) is not None and _coerce_nonnegative_int(row.get("alignment_region_cell_count"),) > 0:
                _record_error(errors, ("frames", index, key), "must be finite when alignment_region_cell_count > 0")
            if value is not None and (value < 0.0 or value > 1.0 + 1.0e-12):
                _record_warning(warnings, ("frames", index, key), "alignment stats out of [0,1] range")

        if _coerce_finite_float(row.get("align_e1_sq_min")) is not None and _coerce_finite_float(row.get("align_e1_sq_max")) is not None:
            if row["align_e1_sq_min"] > row["align_e1_sq_max"]:
                _record_error(errors, ("frames", index), "align_e1_sq_min > align_e1_sq_max")
        if _coerce_finite_float(row.get("align_e3_sq_min")) is not None and _coerce_finite_float(row.get("align_e3_sq_max")) is not None:
            if row["align_e3_sq_min"] > row["align_e3_sq_max"]:
                _record_error(errors, ("frames", index), "align_e3_sq_min > align_e3_sq_max")

        align_e1_sq_sum = _coerce_finite_float(row.get("align_e1_sq_sum"))
        align_e3_sq_sum = _coerce_finite_float(row.get("align_e3_sq_sum"))
        align_e1_sq_mean = _coerce_finite_float(row.get("align_e1_sq_mean"))
        align_e3_sq_mean = _coerce_finite_float(row.get("align_e3_sq_mean"))

        if align_e1_sq_sum is not None and align_region is not None and align_region > 0:
            expected_e1 = _coerce_finite_float(row.get("align_e1_sq_mean"))
            if expected_e1 is not None:
                if abs(expected_e1 - (align_e1_sq_sum / float(align_region))) > 1.0e-12:
                    _record_error(
                        errors,
                        ("frames", index, "align_e1_sq_mean"),
                        "must equal align_e1_sq_sum / alignment_region_cell_count",
                    )
        if align_e3_sq_sum is not None and align_region is not None and align_region > 0:
            expected_e3 = _coerce_finite_float(row.get("align_e3_sq_mean"))
            if expected_e3 is not None:
                if abs(expected_e3 - (align_e3_sq_sum / float(align_region))) > 1.0e-12:
                    _record_error(
                        errors,
                        ("frames", index, "align_e3_sq_mean"),
                        "must equal align_e3_sq_sum / alignment_region_cell_count",
                    )

        if status in {ERROR_STATUS, MISSING_REQUIRED_STATUS}:
            row_errors = row.get("errors")
            if row_errors is not None and not isinstance(row_errors, list):
                _record_error(errors, ("frames", index, "errors"), "must be a list if present")
            if row_errors is None:
                _record_warning(warnings, ("frames", index, "errors"), "no row errors recorded")


def _validate_frames(payload: dict[str, Any], errors: list[str], warnings: list[str]) -> tuple[int, dict[str, int]]:
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

        _validate_frame_row(row, index, errors, warnings)
    return ok_rows, status_counts


def _validate_aggregate(
    payload: dict[str, Any],
    rows: list[Any],
    status_counts: dict[str, int],
    errors: list[str],
    warnings: list[str],
) -> None:
    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        _record_error(errors, ("aggregate",), "must be an object")
        return

    if aggregate.get("processed_frames") != len(rows):
        _record_error(errors, ("aggregate", "processed_frames"), f"expected {len(rows)!r}")
    for key in ("ok_frames", "partial_frames", "missing_frames", "error_frames"):
        if aggregate.get(key) != status_counts[key]:
            _record_error(errors, ("aggregate", key), f"must match computed {key} {status_counts[key]!r}")

    expected = {
        "global_lambda2_positive_count": 0,
        "global_lambda2_negative_count": 0,
        "global_lambda2_zero_count": 0,
        "global_lambda2_region_cell_count": 0,
        "global_alignment_region_cell_count": 0,
        "global_align_e1_count": 0,
        "global_align_e3_count": 0,
        "global_align_tie_count": 0,
        "global_align_rule_success_count": 0,
        "global_align_rule_mismatch_count": 0,
    }
    expected_cell = 0
    expected_finite = 0
    expected_e1_sum = 0.0
    expected_e3_sum = 0.0

    for row in rows:
        if not isinstance(row, dict):
            continue
        expected_cell += int(row.get("cell_count", 0))
        expected_finite += int(row.get("finite_cell_count", 0))
        for row_key, agg_key in (
            ("lambda2_positive_count", "global_lambda2_positive_count"),
            ("lambda2_negative_count", "global_lambda2_negative_count"),
            ("lambda2_zero_count", "global_lambda2_zero_count"),
            ("lambda2_region_cell_count", "global_lambda2_region_cell_count"),
            ("alignment_region_cell_count", "global_alignment_region_cell_count"),
            ("align_e1_count", "global_align_e1_count"),
            ("align_e3_count", "global_align_e3_count"),
            ("align_tie_count", "global_align_tie_count"),
            ("align_rule_success_count", "global_align_rule_success_count"),
            ("align_rule_mismatch_count", "global_align_rule_mismatch_count"),
        ):
            expected[agg_key] += int(row.get(row_key, 0))
        expected_e1_sum += float(row.get("align_e1_sq_sum", 0.0))
        expected_e3_sum += float(row.get("align_e3_sq_sum", 0.0))

    if _coerce_nonnegative_int(aggregate.get("global_cell_count")) != expected_cell:
        _record_error(errors, ("aggregate", "global_cell_count"), f"expected {expected_cell!r}")
    if _coerce_nonnegative_int(aggregate.get("global_finite_cell_count")) != expected_finite:
        _record_error(errors, ("aggregate", "global_finite_cell_count"), f"expected {expected_finite!r}")

    for key, expected_value in expected.items():
        if _coerce_nonnegative_int(aggregate.get(key)) != expected_value:
            _record_error(errors, ("aggregate", key), f"expected {expected_value!r}")

    global_region = _coerce_nonnegative_int(aggregate.get("global_alignment_region_cell_count"))
    if (
        global_region is not None
        and _coerce_nonnegative_int(aggregate.get("global_lambda2_region_cell_count")) is not None
    ):
        if aggregate.get("global_align_e1_count", 0) + aggregate.get("global_align_e3_count", 0) + aggregate.get(
            "global_align_tie_count", 0
        ) != global_region:
            _record_error(
                errors,
                ("aggregate",),
                "global alignment counts must sum to global_alignment_region_cell_count",
            )
        if aggregate.get("global_align_rule_success_count", 0) + aggregate.get("global_align_rule_mismatch_count", 0) != global_region:
            _record_error(
                errors,
                ("aggregate",),
                "global align_rule counts must sum to global_alignment_region_cell_count",
            )
        if aggregate.get("global_align_rule_success_count", 0) != (
            aggregate.get("global_align_e1_count", 0) + aggregate.get("global_align_e3_count", 0)
        ):
            _record_error(
                errors,
                ("aggregate",),
                "global_align_rule_success_count must equal global_align_e1_count + global_align_e3_count",
            )
        if aggregate.get("global_align_rule_mismatch_count", 0) != aggregate.get("global_align_tie_count", 0):
            _record_error(errors, ("aggregate",), "global_align_rule_mismatch_count must equal global_align_tie_count")
        if _coerce_nonnegative_int(aggregate.get("global_lambda2_region_cell_count")) > _coerce_nonnegative_int(
            aggregate.get("global_finite_cell_count")
        ):
            _record_error(
                errors,
                ("aggregate", "global_lambda2_region_cell_count"),
                "global lambda2 region count cannot exceed global finite cell count",
            )

    global_finite = int(_coerce_nonnegative_int(aggregate.get("global_finite_cell_count")) or 0)
    if (
        global_region is not None
        and _coerce_nonnegative_int(aggregate.get("global_lambda2_region_cell_count")) is not None
        and global_region > global_finite
    ):
        _record_error(
            errors,
            ("aggregate",),
            "global_alignment_region_cell_count cannot exceed global_finite_cell_count",
        )

    for fraction_key, count_key in (
        ("global_lambda2_positive_fraction", "global_lambda2_positive_count"),
        ("global_lambda2_negative_fraction", "global_lambda2_negative_count"),
        ("global_lambda2_zero_fraction", "global_lambda2_zero_count"),
    ):
        fraction = _coerce_finite_float(aggregate.get(fraction_key))
        count = _coerce_nonnegative_int(aggregate.get(count_key)) or 0
        expected_fraction = float(count) / float(global_finite) if global_finite > 0 else 0.0
        if fraction is None:
            _record_error(errors, ("aggregate", fraction_key), "must be finite")
            continue
        if fraction < 0.0 or fraction > 1.0:
            _record_warning(warnings, ("aggregate", fraction_key), "outside [0,1]")
        if abs(fraction - expected_fraction) > 1.0e-12:
            _record_error(
                errors,
                ("aggregate", fraction_key),
                f"expected {expected_fraction!r}, got {fraction!r}",
            )

    global_region_fraction_denom = int(_coerce_nonnegative_int(aggregate.get("global_alignment_region_cell_count")) or 0)
    for fraction_key, count_key in (
        ("global_align_e1_fraction", "global_align_e1_count"),
        ("global_align_e3_fraction", "global_align_e3_count"),
        ("global_align_tie_fraction", "global_align_tie_count"),
    ):
        fraction = _coerce_finite_float(aggregate.get(fraction_key))
        count = _coerce_nonnegative_int(aggregate.get(count_key)) or 0
        expected_fraction = float(count) / float(global_region_fraction_denom) if global_region_fraction_denom > 0 else 0.0
        if fraction is None:
            _record_error(errors, ("aggregate", fraction_key), "must be finite")
            continue
        if fraction < 0.0 or fraction > 1.0:
            _record_warning(warnings, ("aggregate", fraction_key), "outside [0,1]")
        if abs(fraction - expected_fraction) > 1.0e-12:
            _record_error(
                errors,
                ("aggregate", fraction_key),
                f"expected {expected_fraction!r}, got {fraction!r}",
            )

    if global_region is not None:
        if not math.isclose(
            _coerce_finite_float(aggregate.get("global_align_e1_sq_sum")) or 0.0,
            expected_e1_sum,
            rel_tol=1e-12,
            abs_tol=1e-12,
        ):
            _record_error(
                errors,
                ("aggregate", "global_align_e1_sq_sum"),
                f"expected {expected_e1_sum!r}",
            )
        if not math.isclose(
            _coerce_finite_float(aggregate.get("global_align_e3_sq_sum")) or 0.0,
            expected_e3_sum,
            rel_tol=1e-12,
            abs_tol=1e-12,
        ):
            _record_error(
                errors,
                ("aggregate", "global_align_e3_sq_sum"),
                f"expected {expected_e3_sum!r}",
            )

    global_align_e1_mean = _coerce_finite_float(aggregate.get("global_align_e1_sq_mean"))
    global_align_e3_mean = _coerce_finite_float(aggregate.get("global_align_e3_sq_mean"))
    if global_region_fraction_denom > 0:
        expected_e1_mean = _coerce_finite_float(aggregate.get("global_align_e1_sq_sum"))
        if expected_e1_mean is not None and global_align_e1_mean is not None and abs(global_align_e1_mean - expected_e1_mean / global_region_fraction_denom) > 1.0e-12:
            _record_error(errors, ("aggregate", "global_align_e1_sq_mean"), "must equal global_align_e1_sq_sum / global_alignment_region_cell_count")
        expected_e3_mean = _coerce_finite_float(aggregate.get("global_align_e3_sq_sum"))
        if expected_e3_mean is not None and global_align_e3_mean is not None and abs(global_align_e3_mean - expected_e3_mean / global_region_fraction_denom) > 1.0e-12:
            _record_error(errors, ("aggregate", "global_align_e3_sq_mean"), "must equal global_align_e3_sq_sum / global_alignment_region_cell_count")
        for fraction_key, count_key in (
            ("global_align_rule_success_fraction", "global_align_rule_success_count"),
            ("global_align_rule_mismatch_fraction", "global_align_rule_mismatch_count"),
        ):
            fraction = _coerce_finite_float(aggregate.get(fraction_key))
            count = _coerce_nonnegative_int(aggregate.get(count_key)) or 0
            expected_fraction = float(count) / float(global_region_fraction_denom) if global_region_fraction_denom > 0 else 0.0
            if fraction is None:
                _record_error(errors, ("aggregate", fraction_key), "must be finite")
                continue
            if fraction < 0.0 or fraction > 1.0:
                _record_warning(warnings, ("aggregate", fraction_key), "outside [0,1]")
            if abs(fraction - expected_fraction) > 1.0e-12:
                _record_error(
                    errors,
                    ("aggregate", fraction_key),
                    f"expected {expected_fraction!r}, got {fraction!r}",
                )
    else:
        if global_align_e1_mean not in (None, 0.0):
            _record_error(errors, ("aggregate", "global_align_e1_sq_mean"), "must be 0.0 when no alignment cells")
        if global_align_e3_mean not in (None, 0.0):
            _record_error(errors, ("aggregate", "global_align_e3_sq_mean"), "must be 0.0 when no alignment cells")

    for key in (
        "global_align_e1_sq_min",
        "global_align_e1_sq_max",
        "global_align_e3_sq_min",
        "global_align_e3_sq_max",
    ):
        if global_region_fraction_denom > 0 and _coerce_finite_float(aggregate.get(key)) is None:
            _record_error(errors, ("aggregate", key), "must be finite when alignment region nonempty")
        if global_region_fraction_denom == 0 and key in aggregate and aggregate.get(key) is not None:
            _record_warning(warnings, ("aggregate", key), "global min/max should remain null when no alignment cells")

    if _coerce_finite_float(aggregate.get("global_align_e1_sq_min")) is not None and _coerce_finite_float(aggregate.get("global_align_e1_sq_max")) is not None:
        if aggregate.get("global_align_e1_sq_min") > aggregate.get("global_align_e1_sq_max"):
            _record_error(errors, ("aggregate",), "global_align_e1_sq_min > global_align_e1_sq_max")
    if _coerce_finite_float(aggregate.get("global_align_e3_sq_min")) is not None and _coerce_finite_float(aggregate.get("global_align_e3_sq_max")) is not None:
        if aggregate.get("global_align_e3_sq_min") > aggregate.get("global_align_e3_sq_max"):
            _record_error(errors, ("aggregate",), "global_align_e3_sq_min > global_align_e3_sq_max")

    if global_region_fraction_denom > 0:
        if _coerce_finite_float(aggregate.get("global_align_e1_sq_min")) is not None and (
            not (0.0 <= float(aggregate["global_align_e1_sq_min"]) <= float(aggregate.get("global_align_e1_sq_max")))
        ):
            _record_warning(warnings, ("aggregate", "global_align_e1_sq_min"), "min/max out of range ordering")
        if _coerce_finite_float(aggregate.get("global_align_e3_sq_min")) is not None and (
            not (0.0 <= float(aggregate["global_align_e3_sq_min"]) <= float(aggregate.get("global_align_e3_sq_max")))
        ):
            _record_warning(warnings, ("aggregate", "global_align_e3_sq_min"), "min/max out of range ordering")


def _validate(payload: dict[str, Any]) -> tuple[list[str], list[str], dict[str, Any]]:
    errors: list[str] = []
    warnings: list[str] = []

    _check_control_card(payload, errors)
    _check_contract(payload, errors)
    _check_route(payload, errors)
    _check_status(payload, errors)
    _check_authority(payload, errors)
    _check_inputs(payload, warnings, errors)

    rows = payload.get("frames")
    ok_rows, status_counts = _validate_frames(payload, errors, warnings)
    if isinstance(rows, list):
        _validate_aggregate(payload, rows, status_counts, errors, warnings)

    details = {
        "status": payload.get("status"),
        "row_count": len(rows) if isinstance(rows, list) else 0,
        "ok_rows": ok_rows,
        "status_counts": status_counts,
    }
    return errors, warnings, details


def main() -> int:
    args = _parse_args()
    try:
        payload = _load_json(args.scan_json)
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        output_payload = {
            "contract": CONTRACT,
            **CONTROL_CARD,
            "status": ERROR_STATUS,
            "input_json": str(args.scan_json),
            "input": {"scan_json": str(args.scan_json), "output_json": str(args.output_json)},
            "details": {},
            "warnings": [],
            "errors": [str(exc)],
            "changed_files": [str(args.scan_json)],
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        output_text = json.dumps(output_payload, sort_keys=True, indent=2 if args.pretty else None, allow_nan=False) + "\n"
        args.output_json.write_text(output_text, encoding="utf-8")
        print(output_text, end="")
        return 1

    errors, warnings, details = _validate(payload)
    output_payload = {
        "contract": CONTRACT,
        "status": ERROR_STATUS if errors else OK_STATUS,
        **CONTROL_CARD,
        "input_json": str(args.scan_json),
        "input": {"scan_json": str(args.scan_json), "output_json": str(args.output_json)},
        "details": details,
        "warnings": warnings,
        "errors": errors,
        "changed_files": [str(args.scan_json), str(args.output_json)],
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    output_text = json.dumps(output_payload, sort_keys=True, indent=2 if args.pretty else None, allow_nan=False) + "\n"
    args.output_json.write_text(output_text, encoding="utf-8")
    print(output_text, end="")
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
