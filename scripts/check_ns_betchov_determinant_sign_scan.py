#!/usr/bin/env python3
"""Validate the corrected Betchov determinant sign scan contract."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_betchov_determinant_sign_scan.py"
CONTRACT = "check_ns_betchov_determinant_sign_scan"
SCAN_CONTRACT = "ns_betchov_determinant_sign_scan"
SCAN_ROUTE_DECISION = "FAIL_CLOSED_BETCHOV_DETERMINANT_SIGN_SCAN"

DEFAULT_INPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_betchov_determinant_sign_scan_N128_20260620.json"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_betchov_determinant_sign_scan_check_N128_20260620.json"
)

CHECK_CARD_KEYS = ("O", "R", "C", "S", "L", "P", "G", "F")
SCAN_REQUIRED_INPUT_KEYS = ("derived_archive", "raw_archive", "frame", "frame_limit", "zero_eps")

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
MISSING_REQUIRED_STATUS = "missing_required_field"
ERROR_STATUS = "error"

ALLOWED_SCAN_STATUS = {OK_STATUS, PARTIAL_STATUS, MISSING_REQUIRED_STATUS, ERROR_STATUS}

COUNT_KEYS = (
    "lambda2_positive_count",
    "lambda2_negative_count",
    "lambda2_zero_count",
    "det_positive_count",
    "det_negative_count",
    "det_zero_count",
    "mismatch_count",
)

FRACTION_KEYS = (
    ("lambda2_positive_fraction", "lambda2_positive_count"),
    ("lambda2_negative_fraction", "lambda2_negative_count"),
    ("lambda2_zero_fraction", "lambda2_zero_count"),
    ("det_positive_fraction", "det_positive_count"),
    ("det_negative_fraction", "det_negative_count"),
    ("det_zero_fraction", "det_zero_count"),
    ("mismatch_fraction", "mismatch_count"),
)

CONTROL_CARD = {
    "O": "Validate the corrected Betchov determinant sign scan contract.",
    "R": (
        "Require contract keys, authority invariants, per-frame sign counts/fractions, "
        "mismatch accounting, and aggregate consistency."
    ),
    "C": SCRIPT_NAME,
    "S": (
        "Fail-closed checker: malformed schema, authority drift, count/fraction mismatches, "
        "or aggregate inconsistencies produce error status."
    ),
    "L": "Load scan JSON, validate telemetry arithmetic and frame/aggregate invariants, then emit checker JSON.",
    "P": "FAIL_CLOSED_BETCHOV_DETERMINANT_SIGN_SCAN_CHECK",
    "G": "This checker validates empirical telemetry only and does not promote any theorem or Clay claim.",
    "F": "Missing lambda2/det(S) data and partial/missing scan status are contract-valid when explicitly stated.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scan-json", type=Path, default=DEFAULT_INPUT, help="Path to scan JSON.")
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT, help="Checker output path.")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output.")
    return parser.parse_args()


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing input file: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"top-level payload is not an object: {path}")
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
        value_f = float(value)
    elif isinstance(value, str):
        try:
            value_f = float(value.strip())
        except ValueError:
            return None
    else:
        return None
    return value_f if math.isfinite(value_f) else None


def _coerce_nonnegative_int(value: Any) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if isinstance(value, float) and math.isfinite(value) and value.is_integer():
        parsed = int(value)
        return parsed if parsed >= 0 else None
    return None


def _check_control_card(payload: dict[str, Any], errors: list[str]) -> None:
    for key in CHECK_CARD_KEYS:
        value = payload.get(key)
        if not isinstance(value, str) or not value.strip():
            _record_error(errors, (key,), f"must be non-empty string")


def _check_contract(payload: dict[str, Any], errors: list[str]) -> None:
    if payload.get("contract") != SCAN_CONTRACT:
        _record_error(errors, ("contract",), f"must be {SCAN_CONTRACT!r}")


def _check_route(payload: dict[str, Any], warnings: list[str], errors: list[str]) -> None:
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
        if not isinstance(actual, bool):
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

    derived = inputs.get("derived_archive")
    if not isinstance(derived, str) or not derived.strip():
        _record_error(errors, ("inputs", "derived_archive"), "must be non-empty string")
    raw = inputs.get("raw_archive")
    if raw is not None and not isinstance(raw, str):
        _record_error(errors, ("inputs", "raw_archive"), "must be null or string")

    frame = inputs.get("frame")
    if frame is not None and _coerce_nonnegative_int(frame) is None:
        _record_error(errors, ("inputs", "frame"), "must be null or nonnegative integer")
    frame_limit = inputs.get("frame_limit")
    if frame_limit is not None and _coerce_nonnegative_int(frame_limit) is None:
        _record_error(errors, ("inputs", "frame_limit"), "must be null or nonnegative integer")
    zero_eps = _coerce_finite_float(inputs.get("zero_eps"))
    if zero_eps is None or zero_eps < 0.0:
        _record_error(errors, ("inputs", "zero_eps"), "must be finite nonnegative number")


def _check_index_path(value: Any, path: tuple[Any, ...], errors: list[str]) -> None:
    if not isinstance(value, list) or len(value) != 3:
        _record_error(errors, path, "must be a 3-element index list")
        return
    for i, item in enumerate(value):
        if not isinstance(item, int) or item < 0:
            _record_error(errors, path + (i,), "must be nonnegative int")


def _validate_frame_row(row: dict[str, Any], index: int, errors: list[str], warnings: list[str]) -> int:
    status = row.get("status")
    if status not in ALLOWED_SCAN_STATUS:
        _record_error(errors, ("frames", index, "status"), f"unexpected status {status!r}")

    frame = _coerce_nonnegative_int(row.get("frame"))
    snapshot = _coerce_nonnegative_int(row.get("snapshot_index"))
    if frame is None:
        _record_error(errors, ("frames", index, "frame"), "must be nonnegative int")
    if snapshot is None:
        _record_error(errors, ("frames", index, "snapshot_index"), "must be nonnegative int")

    if status == OK_STATUS:
        cell_count = _coerce_nonnegative_int(row.get("cell_count"))
        valid_count = _coerce_nonnegative_int(row.get("valid_cell_count"))
        if cell_count is None:
            _record_error(errors, ("frames", index, "cell_count"), "must be nonnegative int")
        if valid_count is None:
            _record_error(errors, ("frames", index, "valid_cell_count"), "must be nonnegative int")
        if isinstance(cell_count, int) and isinstance(valid_count, int) and valid_count > cell_count:
            _record_error(
                errors,
                ("frames", index),
                f"valid_cell_count {valid_count} cannot exceed cell_count {cell_count}",
            )

        if row.get("lambda2_positive_count") is None:
            _record_error(errors, ("frames", index), "lambda2 counts are required for ok rows")
            return OK_STATUS

        lambda2_pos = _coerce_nonnegative_int(row.get("lambda2_positive_count"))
        lambda2_neg = _coerce_nonnegative_int(row.get("lambda2_negative_count"))
        lambda2_zero = _coerce_nonnegative_int(row.get("lambda2_zero_count"))
        det_pos = _coerce_nonnegative_int(row.get("det_positive_count"))
        det_neg = _coerce_nonnegative_int(row.get("det_negative_count"))
        det_zero = _coerce_nonnegative_int(row.get("det_zero_count"))
        mismatch_count = _coerce_nonnegative_int(row.get("mismatch_count"))

        for key in (
            "lambda2_positive_count",
            "lambda2_negative_count",
            "lambda2_zero_count",
            "det_positive_count",
            "det_negative_count",
            "det_zero_count",
            "mismatch_count",
        ):
            if _coerce_nonnegative_int(row.get(key)) is None:
                _record_error(errors, ("frames", index, key), "must be nonnegative integer")

        if (
            lambda2_pos is not None
            and lambda2_neg is not None
            and lambda2_zero is not None
            and valid_count is not None
            and lambda2_pos + lambda2_neg + lambda2_zero != valid_count
        ):
            _record_error(
                errors,
                ("frames", index),
                f"lambda2 counts must sum to valid_cell_count ({valid_count})",
            )
        if (
            det_pos is not None
            and det_neg is not None
            and det_zero is not None
            and valid_count is not None
            and det_pos + det_neg + det_zero != valid_count
        ):
            _record_error(
                errors,
                ("frames", index),
                f"det counts must sum to valid_cell_count ({valid_count})",
            )
        if mismatch_count is not None and valid_count is not None and mismatch_count > valid_count:
            _record_error(errors, ("frames", index, "mismatch_count"), "cannot exceed valid_cell_count")

        for fraction_key, count_key in FRACTION_KEYS:
            fraction = _coerce_finite_float(row.get(fraction_key))
            if fraction is None:
                _record_error(errors, ("frames", index, fraction_key), "must be finite")
                continue
            if fraction < 0.0 or fraction > 1.0:
                _record_warning(warnings, ("frames", index, fraction_key), "fraction outside [0,1]")
            count = _coerce_nonnegative_int(row.get(count_key))
            if count is not None and valid_count is not None:
                expected = float(count) / float(valid_count) if valid_count > 0 else 0.0
                if abs(fraction - expected) > 1.0e-12:
                    _record_error(
                        errors,
                        ("frames", index, fraction_key),
                        f"expected {expected!r} from {count!r}/{valid_count!r}, got {fraction!r}",
                    )

        for key in ("lambda2_min", "lambda2_max", "det_min", "det_max"):
            value = _coerce_finite_float(row.get(key))
            if value is None:
                _record_error(errors, ("frames", index, key), "must be finite")
        if (
            _coerce_finite_float(row.get("lambda2_min")) is not None
            and _coerce_finite_float(row.get("lambda2_max")) is not None
            and row.get("lambda2_min") > row.get("lambda2_max")
        ):
            _record_error(errors, ("frames", index), "lambda2_min > lambda2_max")
        if (
            _coerce_finite_float(row.get("det_min")) is not None
            and _coerce_finite_float(row.get("det_max")) is not None
            and row.get("det_min") > row.get("det_max")
        ):
            _record_error(errors, ("frames", index), "det_min > det_max")

        for key in ("lambda2_argmin", "lambda2_argmax", "det_argmin", "det_argmax"):
            _check_index_path(row.get(key), ("frames", index, key), errors)
        for key in ("lambda2_source", "det_source"):
            source = row.get(key)
            if not isinstance(source, str) or not source.strip():
                _record_warning(warnings, ("frames", index, key), f"missing {key} in ok row")

    if status in {PARTIAL_STATUS, MISSING_REQUIRED_STATUS, ERROR_STATUS}:
        row_errors = row.get("errors")
        if row_errors is not None and not isinstance(row_errors, list):
            _record_error(errors, ("frames", index, "errors"), "must be a list if present")

    return int(status == OK_STATUS)


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
            status_counts["error_frames"] = status_counts.get("error_frames", 0) + 1
            continue
        status = row.get("status")
        if status == OK_STATUS:
            status_counts["ok_frames"] += 1
            ok_rows += _validate_frame_row(row, index, errors, warnings)
        elif status == PARTIAL_STATUS:
            status_counts["partial_frames"] += 1
            _validate_frame_row(row, index, errors, warnings)
        elif status == MISSING_REQUIRED_STATUS:
            status_counts["missing_frames"] += 1
            _validate_frame_row(row, index, errors, warnings)
        elif status == ERROR_STATUS:
            status_counts["error_frames"] += 1
            _validate_frame_row(row, index, errors, warnings)
        else:
            status_counts["error_frames"] += 1
            _record_error(errors, ("frames", index, "status"), f"unexpected status {status!r}")

    return ok_rows, status_counts


def _validate_aggregate(
    payload: dict[str, Any],
    rows: list[Any],
    ok_rows: int,
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
    if aggregate.get("ok_frames") != status_counts["ok_frames"]:
        _record_error(
            errors,
            ("aggregate", "ok_frames"),
            f"must match frame status count {status_counts['ok_frames']!r}",
        )
    if aggregate.get("partial_frames") != status_counts["partial_frames"]:
        _record_error(
            errors,
            ("aggregate", "partial_frames"),
            f"must match frame status count {status_counts['partial_frames']!r}",
        )
    if aggregate.get("missing_frames") != status_counts["missing_frames"]:
        _record_error(
            errors,
            ("aggregate", "missing_frames"),
            f"must match frame status count {status_counts['missing_frames']!r}",
        )
    if aggregate.get("error_frames") != status_counts["error_frames"]:
        _record_error(
            errors,
            ("aggregate", "error_frames"),
            f"must match frame status count {status_counts['error_frames']!r}",
        )

    row_global_count = {
        "global_lambda2_positive_count": 0,
        "global_lambda2_negative_count": 0,
        "global_lambda2_zero_count": 0,
        "global_det_positive_count": 0,
        "global_det_negative_count": 0,
        "global_det_zero_count": 0,
        "global_mismatch_count": 0,
    }
    expected_valid = 0
    for row in rows:
        if not isinstance(row, dict):
            continue
        for row_key, agg_key in (
            ("lambda2_positive_count", "global_lambda2_positive_count"),
            ("lambda2_negative_count", "global_lambda2_negative_count"),
            ("lambda2_zero_count", "global_lambda2_zero_count"),
            ("det_positive_count", "global_det_positive_count"),
            ("det_negative_count", "global_det_negative_count"),
            ("det_zero_count", "global_det_zero_count"),
            ("mismatch_count", "global_mismatch_count"),
        ):
            value = _coerce_nonnegative_int(row.get(row_key))
            if value is not None:
                row_global_count[agg_key] += value
        valid_cell_count = _coerce_nonnegative_int(row.get("valid_cell_count"))
        if valid_cell_count is not None:
            expected_valid += valid_cell_count

    for key, expected in row_global_count.items():
        if aggregate.get(key) != expected:
            _record_error(errors, ("aggregate", key), f"expected {expected!r}")

    aggregate_valid = _coerce_nonnegative_int(aggregate.get("global_valid_cell_count")) or 0
    if aggregate_valid != expected_valid:
        _record_error(errors, ("aggregate", "global_valid_cell_count"), f"expected {expected_valid!r}")

    fraction_specs = (
        ("global_lambda2_positive_fraction", "global_lambda2_positive_count"),
        ("global_lambda2_negative_fraction", "global_lambda2_negative_count"),
        ("global_lambda2_zero_fraction", "global_lambda2_zero_count"),
        ("global_det_positive_fraction", "global_det_positive_count"),
        ("global_det_negative_fraction", "global_det_negative_count"),
        ("global_det_zero_fraction", "global_det_zero_count"),
        ("global_mismatch_fraction", "global_mismatch_count"),
    )
    for fraction_key, count_key in fraction_specs:
        fraction = _coerce_finite_float(aggregate.get(fraction_key))
        count = _coerce_nonnegative_int(aggregate.get(count_key)) or 0
        if fraction is None:
            _record_error(errors, ("aggregate", fraction_key), "must be finite")
            continue
        if fraction < 0.0 or fraction > 1.0:
            _record_warning(warnings, ("aggregate", fraction_key), "outside [0,1]")
        expected = float(count) / float(aggregate_valid) if aggregate_valid > 0 else 0.0
        if abs(fraction - expected) > 1.0e-12:
            _record_error(
                errors,
                ("aggregate", fraction_key),
                f"expected {expected!r} from {count!r}/{aggregate_valid!r}, got {fraction!r}",
            )

    for key in ("global_lambda2_min", "global_lambda2_max", "global_det_min", "global_det_max"):
        value = aggregate.get(key)
        if value is not None and _coerce_finite_float(value) is None:
            _record_error(errors, ("aggregate", key), "must be finite if present")


def _validate(payload: dict[str, Any]) -> tuple[list[str], list[str], dict[str, Any]]:
    errors: list[str] = []
    warnings: list[str] = []

    _check_control_card(payload, errors)
    _check_contract(payload, errors)
    _check_route(payload, warnings, errors)
    _check_status(payload, errors)
    _check_authority(payload, errors)
    _check_inputs(payload, warnings, errors)

    rows = payload.get("frames")
    ok_rows, status_counts = _validate_frames(payload, errors, warnings)
    if isinstance(rows, list):
        _validate_aggregate(payload, rows, ok_rows, status_counts, errors, warnings)

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
        result = {
            "contract": CONTRACT,
            **CONTROL_CARD,
            "control_card": CONTROL_CARD,
            "status": ERROR_STATUS,
            "input_json": str(args.scan_json),
            "input": {"scan_json": str(args.scan_json), "output_json": str(args.output_json)},
            "details": {},
            "warnings": [],
            "errors": [str(exc)],
            "changed_files": [str(args.scan_json)],
        }
        output = json.dumps(result, sort_keys=True, indent=2 if args.pretty else None, allow_nan=False) + "\n"
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(output, encoding="utf-8")
        print(output, end="")
        return 1

    errors, warnings, details = _validate(payload)
    output_payload = {
        "contract": CONTRACT,
        "status": ERROR_STATUS if errors else OK_STATUS,
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
        "input_json": str(args.scan_json),
        "input": {"scan_json": str(args.scan_json), "output_json": str(args.output_json)},
        "details": details,
        "warnings": warnings,
        "errors": errors,
        "changed_files": [str(args.scan_json), str(args.output_json)],
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    output = json.dumps(output_payload, sort_keys=True, indent=2 if args.pretty else None, allow_nan=False) + "\n"
    args.output_json.write_text(output, encoding="utf-8")
    print(output, end="")
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
