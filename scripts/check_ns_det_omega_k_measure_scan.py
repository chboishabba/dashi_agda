#!/usr/bin/env python3
"""Validate the corrected Omega_K determinant-side sign scan contract."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_det_omega_k_measure_scan.py"
CONTRACT = "check_ns_det_omega_k_measure_scan"
SCAN_CONTRACT = "ns_det_omega_k_measure_scan"
SCAN_ROUTE_DECISION = "FAIL_CLOSED_NS_DET_OMEGA_K_MEASURE_SCAN"
SCAN_CHECK_ROUTE = "FAIL_CLOSED_NS_DET_OMEGA_K_MEASURE_SCAN_CHECK"

DEFAULT_SCAN_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_det_omega_k_measure_scan_N128_20260620.json"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_det_omega_k_measure_scan_check_N128_20260620.json"
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
    "det_positive_count",
    "det_negative_count",
    "det_zero_count",
    "mismatch_lambda2_negative_det_nonpositive_count",
    "mismatch_lambda2_positive_det_nonnegative_count",
    "mismatch_count",
)

FRACTION_KEYS = (
    ("lambda2_positive_fraction", "lambda2_positive_count"),
    ("lambda2_negative_fraction", "lambda2_negative_count"),
    ("lambda2_zero_fraction", "lambda2_zero_count"),
    ("det_positive_fraction", "det_positive_count"),
    ("det_negative_fraction", "det_negative_count"),
    ("det_zero_fraction", "det_zero_count"),
    ("mismatch_lambda2_negative_det_nonpositive_fraction", "mismatch_lambda2_negative_det_nonpositive_count"),
    ("mismatch_lambda2_positive_det_nonnegative_fraction", "mismatch_lambda2_positive_det_nonnegative_count"),
    ("mismatch_fraction", "mismatch_count"),
)

CONTROL_CARD = {
    "O": "Validate the corrected Omega_K determinant-side sign scan contract.",
    "R": "Validate frame and aggregate sign-bucket/mismatch counts, fractions, and consistency invariants.",
    "C": SCRIPT_NAME,
    "S": "Fail-closed checker: schema mismatch, count arithmetic mismatch, or invalid fractions mark error.",
    "L": "Load the scan JSON, validate control-card/authority invariants, and emit compact checker telemetry.",
    "P": SCAN_CHECK_ROUTE,
    "G": "Checker is empirical only and does not infer or promote any theorem or Clay claim.",
    "F": "Only explicit status degradation is accepted as partial telemetry; missing/invalid scan fields are errors.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scan-json", type=Path, default=DEFAULT_SCAN_JSON, help="Path to scan JSON.")
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT, help="Output JSON path.")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON.")
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
        parsed = float(value)
    elif isinstance(value, str):
        try:
            parsed = float(value.strip())
        except ValueError:
            return None
    else:
        return None
    if not math.isfinite(parsed):
        return None
    return parsed


def _coerce_nonnegative_int(value: Any) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if isinstance(value, float) and math.isfinite(value) and value.is_integer():
        parsed = int(value)
        return parsed if parsed >= 0 else None
    return None


def _coerce_bool(value: Any) -> bool | None:
    return value if isinstance(value, bool) else None


def _coerce_nonempty_str(value: Any) -> str | None:
    if not isinstance(value, str):
        return None
    text = value.strip()
    return text if text else None

def _coerce_nonnegative_int_list(value: Any) -> list[int] | None:
    if not isinstance(value, list):
        return None
    result: list[int] = []
    for item in value:
        if not isinstance(item, int) or item < 0:
            return None
        result.append(item)
    return result


def _check_control_card(payload: dict[str, Any], errors: list[str]) -> None:
    for key in CHECK_CARD_KEYS:
        value = payload.get(key)
        if _coerce_nonempty_str(value) is None:
            _record_error(errors, (key,), "must be a non-empty string")


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


def _check_inputs(payload: dict[str, Any], errors: list[str], warnings: list[str]) -> None:
    inputs = payload.get("inputs")
    if not isinstance(inputs, dict):
        _record_error(errors, ("inputs",), "must be an object")
        return
    for key in SCAN_REQUIRED_INPUT_KEYS:
        if key not in inputs:
            _record_warning(warnings, ("inputs",), f"missing optional metadata field {key!r}")
    if _coerce_nonempty_str(inputs.get("raw_archive")) is None:
        _record_error(errors, ("inputs", "raw_archive"), "must be non-empty string")
    if inputs.get("frame") is not None and _coerce_nonnegative_int(inputs.get("frame")) is None:
        _record_error(errors, ("inputs", "frame"), "must be null or nonnegative int")
    if inputs.get("frame_limit") is not None and _coerce_nonnegative_int(inputs.get("frame_limit")) is None:
        _record_error(errors, ("inputs", "frame_limit"), "must be null or nonnegative int")
    zero_eps = inputs.get("zero_eps")
    eps = _coerce_finite_float(zero_eps)
    if eps is None or eps < 0.0:
        _record_error(errors, ("inputs", "zero_eps"), "must be finite nonnegative")
    if _coerce_nonnegative_int_list(inputs.get("selected_frames")) is None:
        _record_warning(warnings, ("inputs", "selected_frames"), "must be a list of nonnegative ints if present")


def _check_index_path(value: Any, path: tuple[Any, ...], errors: list[str]) -> None:
    if not isinstance(value, list) or len(value) != 3:
        _record_error(errors, path, "must be a 3-element index list")
        return
    for index, item in enumerate(value):
        if not isinstance(item, int) or item < 0:
            _record_error(errors, path + (index,), "must be nonnegative int")


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
    if source is None and status in {OK_STATUS, PARTIAL_STATUS}:
        _record_error(errors, ("frames", index, "source"), "must be non-empty str for ok/partial rows")

    if status in {OK_STATUS, PARTIAL_STATUS}:
        cell_count = _coerce_nonnegative_int(row.get("cell_count"))
        valid_count = _coerce_nonnegative_int(row.get("valid_cell_count"))
        if cell_count is None:
            _record_error(errors, ("frames", index, "cell_count"), "must be nonnegative int")
        if valid_count is None:
            _record_error(errors, ("frames", index, "valid_cell_count"), "must be nonnegative int")
        if isinstance(cell_count, int) and isinstance(valid_count, int) and valid_count > cell_count:
            _record_error(errors, ("frames", index), "valid_cell_count cannot exceed cell_count")

        for key in COUNT_KEYS:
            if _coerce_nonnegative_int(row.get(key)) is None:
                _record_error(errors, ("frames", index, key), "must be nonnegative int")

        l2_pos = _coerce_nonnegative_int(row.get("lambda2_positive_count"))
        l2_neg = _coerce_nonnegative_int(row.get("lambda2_negative_count"))
        l2_zero = _coerce_nonnegative_int(row.get("lambda2_zero_count"))
        if (
            l2_pos is not None
            and l2_neg is not None
            and l2_zero is not None
            and valid_count is not None
            and l2_pos + l2_neg + l2_zero != valid_count
        ):
            _record_error(
                errors,
                ("frames", index),
                f"lambda2 counts must sum to valid_cell_count ({valid_count})",
            )

        d_pos = _coerce_nonnegative_int(row.get("det_positive_count"))
        d_neg = _coerce_nonnegative_int(row.get("det_negative_count"))
        d_zero = _coerce_nonnegative_int(row.get("det_zero_count"))
        if (
            d_pos is not None
            and d_neg is not None
            and d_zero is not None
            and valid_count is not None
            and d_pos + d_neg + d_zero != valid_count
        ):
            _record_error(
                errors,
                ("frames", index),
                f"det(S) counts must sum to valid_cell_count ({valid_count})",
            )

        mm_neg = _coerce_nonnegative_int(row.get("mismatch_lambda2_negative_det_nonpositive_count"))
        mm_pos = _coerce_nonnegative_int(row.get("mismatch_lambda2_positive_det_nonnegative_count"))
        mismatch = _coerce_nonnegative_int(row.get("mismatch_count"))
        if mismatch is not None and mm_neg is not None and mm_pos is not None and mismatch != mm_neg + mm_pos:
            _record_error(
                errors,
                ("frames", index, "mismatch_count"),
                "must equal mismatch_lambda2_negative_det_nonpositive_count + mismatch_lambda2_positive_det_nonnegative_count",
            )

        if valid_count is not None and mismatch is not None and mismatch > valid_count:
            _record_error(errors, ("frames", index, "mismatch_count"), "cannot exceed valid_cell_count")

        for fraction_key, count_key in FRACTION_KEYS:
            fraction = _coerce_finite_float(row.get(fraction_key))
            if fraction is None:
                _record_error(errors, ("frames", index, fraction_key), "must be finite")
                continue
            if fraction < 0.0 or fraction > 1.0:
                _record_warning(warnings, ("frames", index, fraction_key), "outside [0,1]")
            count = _coerce_nonnegative_int(row.get(count_key))
            if count is not None and valid_count is not None:
                expected = float(count) / float(valid_count) if valid_count > 0 else 0.0
                if abs(fraction - expected) > 1.0e-12:
                    _record_error(
                        errors,
                        ("frames", index, fraction_key),
                        f"expected {expected!r}, got {fraction!r}",
                    )

        for key in ("lambda2_min", "lambda2_max", "det_min", "det_max"):
            value = _coerce_finite_float(row.get(key))
            if value is None:
                _record_error(errors, ("frames", index, key), "must be finite if present")
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
            if _coerce_nonempty_str(row.get(key)) is None:
                _record_warning(warnings, ("frames", index, key), f"missing {key} in ok/partial row")

    elif status in {MISSING_REQUIRED_STATUS, ERROR_STATUS}:
        row_errors = row.get("errors")
        if row_errors is not None and not isinstance(row_errors, list):
            _record_error(errors, ("frames", index, "errors"), "must be a list if present")
        if not row_errors:
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
        "global_det_positive_count": 0,
        "global_det_negative_count": 0,
        "global_det_zero_count": 0,
        "global_mismatch_lambda2_negative_det_nonpositive_count": 0,
        "global_mismatch_lambda2_positive_det_nonnegative_count": 0,
        "global_mismatch_count": 0,
    }
    expected_valid = 0
    expected_cell = 0

    for row in rows:
        if not isinstance(row, dict):
            continue
        expected_cell += int(row.get("cell_count", 0))
        expected_valid += int(row.get("valid_cell_count", 0))
        expected["global_lambda2_positive_count"] += int(row.get("lambda2_positive_count", 0))
        expected["global_lambda2_negative_count"] += int(row.get("lambda2_negative_count", 0))
        expected["global_lambda2_zero_count"] += int(row.get("lambda2_zero_count", 0))
        expected["global_det_positive_count"] += int(row.get("det_positive_count", 0))
        expected["global_det_negative_count"] += int(row.get("det_negative_count", 0))
        expected["global_det_zero_count"] += int(row.get("det_zero_count", 0))
        expected["global_mismatch_lambda2_negative_det_nonpositive_count"] += int(
            row.get("mismatch_lambda2_negative_det_nonpositive_count", 0)
        )
        expected["global_mismatch_lambda2_positive_det_nonnegative_count"] += int(
            row.get("mismatch_lambda2_positive_det_nonnegative_count", 0)
        )
        expected["global_mismatch_count"] += int(row.get("mismatch_count", 0))

    global_valid = _coerce_nonnegative_int(aggregate.get("global_valid_cell_count")) or 0
    if global_valid != expected_valid:
        _record_error(errors, ("aggregate", "global_valid_cell_count"), f"expected {expected_valid!r}")
    global_cell = _coerce_nonnegative_int(aggregate.get("global_cell_count")) or 0
    if global_cell != expected_cell:
        _record_warning(warnings, ("aggregate", "global_cell_count"), f"expected {expected_cell!r}")

    for key, expected_value in expected.items():
        actual = aggregate.get(key)
        if _coerce_nonnegative_int(actual) != expected_value:
            _record_error(errors, ("aggregate", key), f"expected {expected_value!r}")

    if expected["global_mismatch_lambda2_negative_det_nonpositive_count"] + expected[
        "global_mismatch_lambda2_positive_det_nonnegative_count"
    ] != expected["global_mismatch_count"]:
        _record_error(
            errors,
            ("aggregate", "global_mismatch_count"),
            "global mismatch_count must equal mismatch bin sums",
        )

    fraction_specs = (
        ("global_lambda2_positive_fraction", "global_lambda2_positive_count"),
        ("global_lambda2_negative_fraction", "global_lambda2_negative_count"),
        ("global_lambda2_zero_fraction", "global_lambda2_zero_count"),
        ("global_det_positive_fraction", "global_det_positive_count"),
        ("global_det_negative_fraction", "global_det_negative_count"),
        ("global_det_zero_fraction", "global_det_zero_count"),
        (
            "global_mismatch_lambda2_negative_det_nonpositive_fraction",
            "global_mismatch_lambda2_negative_det_nonpositive_count",
        ),
        (
            "global_mismatch_lambda2_positive_det_nonnegative_fraction",
            "global_mismatch_lambda2_positive_det_nonnegative_count",
        ),
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
        expected_value = float(count) / float(global_valid) if global_valid > 0 else 0.0
        if abs(fraction - expected_value) > 1.0e-12:
            _record_error(
                errors,
                ("aggregate", fraction_key),
                f"expected {expected_value!r}, got {fraction!r}",
            )

    for key in ("global_lambda2_min", "global_lambda2_max", "global_det_min", "global_det_max"):
        value = aggregate.get(key)
        if value is not None and _coerce_finite_float(value) is None:
            _record_error(errors, ("aggregate", key), "must be finite if present")
    if (
        _coerce_finite_float(aggregate.get("global_lambda2_min")) is not None
        and _coerce_finite_float(aggregate.get("global_lambda2_max")) is not None
        and aggregate.get("global_lambda2_min") > aggregate.get("global_lambda2_max")
    ):
        _record_error(errors, ("aggregate",), "global lambda2 min > global lambda2 max")
    if (
        _coerce_finite_float(aggregate.get("global_det_min")) is not None
        and _coerce_finite_float(aggregate.get("global_det_max")) is not None
        and aggregate.get("global_det_min") > aggregate.get("global_det_max")
    ):
        _record_error(errors, ("aggregate",), "global det min > global det max")


def _validate(payload: dict[str, Any]) -> tuple[list[str], list[str], dict[str, Any]]:
    errors: list[str] = []
    warnings: list[str] = []

    _check_control_card(payload, errors)
    _check_contract(payload, errors)
    _check_route(payload, errors)
    _check_status(payload, errors)
    _check_authority(payload, errors)
    _check_inputs(payload, errors, warnings)

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
        result = {
            "contract": CONTRACT,
            **CONTROL_CARD,
            "control_card": CONTROL_CARD,
            "status": ERROR_STATUS,
            "input": {"scan_json": str(args.scan_json), "output_json": str(args.output_json)},
            "details": {},
            "warnings": [],
            "errors": [str(exc)],
            "changed_files": [str(args.scan_json)],
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        output_text = json.dumps(result, sort_keys=True, indent=2 if args.pretty else None, allow_nan=False) + "\n"
        args.output_json.write_text(output_text, encoding="utf-8")
        print(output_text, end="")
        return 1

    errors, warnings, details = _validate(payload)
    output_payload = {
        "contract": CONTRACT,
        "status": ERROR_STATUS if errors else OK_STATUS,
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
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
