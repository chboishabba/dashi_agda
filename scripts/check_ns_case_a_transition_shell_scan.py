#!/usr/bin/env python3
"""Strict checker for the Case A transition shell scan contract."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_case_a_transition_shell_scan.py"
CONTRACT = "check_ns_case_a_transition_shell_scan"
SCAN_CONTRACT = "ns_case_a_transition_shell_scan"
SCAN_ROUTE_DECISION = "FAIL_CLOSED_NS_CASE_A_TRANSITION_SHELL_SCAN"
SCAN_CHECK_ROUTE = "FAIL_CLOSED_NS_CASE_A_TRANSITION_SHELL_SCAN_CHECK"

DEFAULT_SCAN_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_case_a_transition_shell_scan_N128_20260621.json"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_case_a_transition_shell_scan_check_N128_20260621.json"
)

CHECK_CARD_KEYS = ("O", "R", "C", "S", "L", "P", "G", "F")

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
MISSING_REQUIRED_STATUS = "missing_required_field"
ERROR_STATUS = "error"
ALLOWED_SCAN_STATUS = {OK_STATUS, PARTIAL_STATUS, MISSING_REQUIRED_STATUS, ERROR_STATUS}

CONTROL_CARD = {
    "O": "Strictly validate the Case A transition shell scan contract.",
    "R": "Validate per-frame and aggregate shell telemetry, band sweeps, threshold rows, and count/fraction arithmetic.",
    "C": SCRIPT_NAME,
    "S": "Fail-closed checker: schema mismatch, count mismatch, invalid fractions, or missing invariants produce error.",
    "L": "Load the scan JSON, validate structure and arithmetic, and emit checker telemetry only.",
    "P": SCAN_CHECK_ROUTE,
    "G": "Checker is empirical only and does not infer any theorem or Clay claim.",
    "F": "The checker enforces telemetry consistency only; it does not promote any mathematical statement.",
}

BENIGN_WARNING_SUFFIXES = (
    "velocity_snapshots axis-1 channel layout detected",
    "velocity_snapshots trailing channel layout detected",
    "velocity_snapshots last-axis channel layout detected",
    "velocity fallback axis-1 channel layout detected",
    "velocity fallback trailing channel layout detected",
    "converted legacy (T,N,N,N,3) velocity layout to components",
    "domain_length unavailable; using fallback",
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scan-json", type=Path, default=DEFAULT_SCAN_JSON, help="Path to scan JSON")
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT, help="Output JSON path")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output")
    return parser.parse_args()


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing input file: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"top-level payload is not an object: {path}")
    return payload


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, ensure_ascii=False, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False)


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


def _coerce_bool(value: Any) -> bool | None:
    return value if isinstance(value, bool) else None


def _coerce_nonempty_str(value: Any) -> str | None:
    if not isinstance(value, str):
        return None
    text = value.strip()
    return text if text else None


def _coerce_nonnegative_float_list(value: Any) -> list[float] | None:
    if not isinstance(value, list):
        return None
    output: list[float] = []
    for item in value:
        parsed = _coerce_finite_float(item)
        if parsed is None or parsed < 0.0:
            return None
        output.append(float(parsed))
    return output


def _coerce_positive_float_list(value: Any) -> list[float] | None:
    if not isinstance(value, list):
        return None
    output: list[float] = []
    for item in value:
        parsed = _coerce_finite_float(item)
        if parsed is None or parsed <= 0.0:
            return None
        output.append(float(parsed))
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


def _check_inputs(payload: dict[str, Any], errors: list[str], warnings: list[str]) -> tuple[list[float], list[float], int]:
    inputs = payload.get("inputs")
    if not isinstance(inputs, dict):
        _record_error(errors, ("inputs",), "must be an object")
        return [], [], 0

    for key in ("raw_archive", "frame", "frame_limit", "zero_eps", "lambda2_band_values", "strain_thresholds", "shell_step_limit", "selected_frames"):
        if key not in inputs:
            _record_warning(warnings, ("inputs",), f"missing optional metadata field {key!r}")

    if _coerce_nonempty_str(inputs.get("raw_archive")) is None:
        _record_error(errors, ("inputs", "raw_archive"), "must be non-empty string")
    if inputs.get("frame") is not None and _coerce_nonnegative_int(inputs.get("frame")) is None:
        _record_error(errors, ("inputs", "frame"), "must be null or nonnegative int")
    if inputs.get("frame_limit") is not None and _coerce_nonnegative_int(inputs.get("frame_limit")) is None:
        _record_error(errors, ("inputs", "frame_limit"), "must be null or nonnegative int")
    if _coerce_finite_float(inputs.get("zero_eps")) is None or float(inputs.get("zero_eps", 0.0)) < 0.0:
        _record_error(errors, ("inputs", "zero_eps"), "must be finite nonnegative")

    lambda2_band_values = _coerce_positive_float_list(inputs.get("lambda2_band_values"))
    if lambda2_band_values is None or not lambda2_band_values:
        _record_error(errors, ("inputs", "lambda2_band_values"), "must be a non-empty list of positive floats")
        lambda2_band_values = []
    elif lambda2_band_values != sorted(lambda2_band_values):
        _record_error(errors, ("inputs", "lambda2_band_values"), "must be sorted ascending")

    strain_thresholds = _coerce_nonnegative_float_list(inputs.get("strain_thresholds"))
    if strain_thresholds is None or not strain_thresholds:
        _record_error(errors, ("inputs", "strain_thresholds"), "must be a non-empty list of nonnegative floats")
        strain_thresholds = []
    elif strain_thresholds != sorted(strain_thresholds):
        _record_error(errors, ("inputs", "strain_thresholds"), "must be sorted ascending")

    shell_step_limit = _coerce_nonnegative_int(inputs.get("shell_step_limit"))
    if shell_step_limit is None or shell_step_limit <= 0:
        _record_error(errors, ("inputs", "shell_step_limit"), "must be positive int")
        shell_step_limit = 0

    if _coerce_nonempty_str(inputs.get("boundary_proxy_selection_policy")) is None:
        _record_error(errors, ("inputs", "boundary_proxy_selection_policy"), "must be non-empty string")
    if _coerce_nonempty_str(inputs.get("shell_metric")) is None:
        _record_error(errors, ("inputs", "shell_metric"), "must be non-empty string")
    if inputs.get("selected_frames") is not None and not isinstance(inputs.get("selected_frames"), list):
        _record_error(errors, ("inputs", "selected_frames"), "must be a list if present")
    elif isinstance(inputs.get("selected_frames"), list):
        for index, item in enumerate(inputs["selected_frames"]):
            if _coerce_nonnegative_int(item) is None:
                _record_error(errors, ("inputs", "selected_frames", index), "must be nonnegative int")

    return lambda2_band_values, strain_thresholds, shell_step_limit


def _check_band_rows(rows: list[Any], finite_cell_count: int, errors: list[str], warnings: list[str]) -> tuple[int | None, float | None]:
    if not isinstance(rows, list):
        _record_error(errors, ("boundary_proxy", "band_rows"), "must be a list")
        return None, None

    selected_count = None
    selected_band = None
    previous_count = None
    selected_true = 0
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            _record_error(errors, ("boundary_proxy", "band_rows", index), "must be an object")
            continue
        band = _coerce_finite_float(row.get("band"))
        count = _coerce_nonnegative_int(row.get("count"))
        fraction = _coerce_finite_float(row.get("fraction"))
        selected = _coerce_bool(row.get("selected"))
        if band is None or band <= 0.0:
            _record_error(errors, ("boundary_proxy", "band_rows", index, "band"), "must be positive finite")
        if count is None:
            _record_error(errors, ("boundary_proxy", "band_rows", index, "count"), "must be nonnegative int")
        if fraction is None:
            _record_error(errors, ("boundary_proxy", "band_rows", index, "fraction"), "must be finite")
        elif fraction < 0.0 or fraction > 1.0:
            _record_warning(warnings, ("boundary_proxy", "band_rows", index, "fraction"), "outside [0,1]")
        if count is not None and fraction is not None:
            expected = float(count) / float(finite_cell_count) if finite_cell_count > 0 else 0.0
            if abs(fraction - expected) > 1.0e-12:
                _record_error(
                    errors,
                    ("boundary_proxy", "band_rows", index, "fraction"),
                    f"expected {expected!r}, got {fraction!r}",
                )
        if selected is None:
            _record_error(errors, ("boundary_proxy", "band_rows", index, "selected"), "must be bool")
        elif selected:
            selected_true += 1
            selected_count = count
            selected_band = band
        if previous_count is not None and count is not None and count < previous_count:
            _record_error(errors, ("boundary_proxy", "band_rows", index, "count"), "counts must be nondecreasing across bands")
        if count is not None:
            previous_count = count

    if selected_true != 1:
        _record_error(errors, ("boundary_proxy", "band_rows"), "exactly one band row must be selected")

    return selected_count, selected_band


def _check_threshold_rows(
    rows: list[Any],
    shell_step_limit: int,
    finite_cell_count: int,
    errors: list[str],
    warnings: list[str],
) -> tuple[list[int], list[int], list[int]]:
    if not isinstance(rows, list):
        _record_error(errors, ("threshold_rows",), "must be a list")
        return [], [], []

    previous_count = None
    counts_totals: list[int] = [0] * (shell_step_limit + 2)
    high_counts: list[int] = []
    overlap_counts: list[int] = []

    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            _record_error(errors, ("threshold_rows", index), "must be an object")
            continue

        k0 = _coerce_finite_float(row.get("k0"))
        high_count = _coerce_nonnegative_int(row.get("high_strain_count"))
        overlap_count = _coerce_nonnegative_int(row.get("high_strain_boundary_overlap_count"))
        fraction = _coerce_finite_float(row.get("high_strain_fraction"))
        overlap_fraction = _coerce_finite_float(row.get("high_strain_boundary_overlap_fraction"))
        shell_limit = _coerce_nonnegative_int(row.get("shell_step_limit"))
        counts = row.get("shell_step_counts")
        fractions = row.get("shell_step_fractions")

        if k0 is None or k0 < 0.0:
            _record_error(errors, ("threshold_rows", index, "k0"), "must be finite and nonnegative")
        if high_count is None:
            _record_error(errors, ("threshold_rows", index, "high_strain_count"), "must be nonnegative int")
        if overlap_count is None:
            _record_error(errors, ("threshold_rows", index, "high_strain_boundary_overlap_count"), "must be nonnegative int")
        if fraction is None:
            _record_error(errors, ("threshold_rows", index, "high_strain_fraction"), "must be finite")
        elif fraction < 0.0 or fraction > 1.0:
            _record_warning(warnings, ("threshold_rows", index, "high_strain_fraction"), "outside [0,1]")
        if overlap_fraction is None:
            _record_error(errors, ("threshold_rows", index, "high_strain_boundary_overlap_fraction"), "must be finite")
        elif overlap_fraction < 0.0 or overlap_fraction > 1.0:
            _record_warning(warnings, ("threshold_rows", index, "high_strain_boundary_overlap_fraction"), "outside [0,1]")
        if shell_limit is None or shell_limit != shell_step_limit:
            _record_error(errors, ("threshold_rows", index, "shell_step_limit"), f"must be {shell_step_limit!r}")

        if not isinstance(counts, list) or len(counts) != shell_step_limit + 2:
            _record_error(errors, ("threshold_rows", index, "shell_step_counts"), f"must be length {shell_step_limit + 2}")
            counts = []
        if not isinstance(fractions, list) or len(fractions) != shell_step_limit + 2:
            _record_error(errors, ("threshold_rows", index, "shell_step_fractions"), f"must be length {shell_step_limit + 2}")
            fractions = []

        if isinstance(counts, list):
            parsed_counts: list[int] = []
            for bucket_index, item in enumerate(counts):
                parsed = _coerce_nonnegative_int(item)
                if parsed is None:
                    _record_error(errors, ("threshold_rows", index, "shell_step_counts", bucket_index), "must be nonnegative int")
                    parsed = 0
                parsed_counts.append(parsed)
            if high_count is not None and sum(parsed_counts) != high_count:
                _record_error(errors, ("threshold_rows", index, "shell_step_counts"), f"must sum to high_strain_count {high_count!r}")
            for bucket_index, item in enumerate(parsed_counts):
                counts_totals[bucket_index] += item
            counts = parsed_counts
        if isinstance(fractions, list):
            parsed_fractions: list[float] = []
            for bucket_index, item in enumerate(fractions):
                parsed = _coerce_finite_float(item)
                if parsed is None:
                    _record_error(errors, ("threshold_rows", index, "shell_step_fractions", bucket_index), "must be finite")
                    parsed = 0.0
                elif parsed < 0.0 or parsed > 1.0:
                    _record_warning(warnings, ("threshold_rows", index, "shell_step_fractions", bucket_index), "outside [0,1]")
                parsed_fractions.append(parsed)
            if high_count is not None and high_count > 0:
                expected = [float(value) / float(high_count) for value in counts]
                for bucket_index, (actual, want) in enumerate(zip(parsed_fractions, expected, strict=True)):
                    if abs(actual - want) > 1.0e-12:
                        _record_error(
                            errors,
                            ("threshold_rows", index, "shell_step_fractions", bucket_index),
                            f"expected {want!r}, got {actual!r}",
                        )
            elif any(parsed_fractions):
                _record_error(errors, ("threshold_rows", index, "shell_step_fractions"), "must be all zeros for empty high-strain rows")

        if high_count is not None and previous_count is not None and high_count > previous_count:
            _record_error(errors, ("threshold_rows", index, "high_strain_count"), "threshold counts must be nonincreasing with K0")
        if high_count is not None:
            previous_count = high_count
            high_counts.append(high_count)
        if overlap_count is not None:
            overlap_counts.append(overlap_count)
            if high_count is not None and overlap_count > high_count:
                _record_error(errors, ("threshold_rows", index, "high_strain_boundary_overlap_count"), "cannot exceed high_strain_count")
            if high_count is not None and overlap_count == 0 and high_count > 0:
                pass
        if finite_cell_count > 0 and fraction is not None and high_count is not None:
            expected = float(high_count) / float(finite_cell_count)
            if abs(fraction - expected) > 1.0e-12:
                _record_error(
                    errors,
                    ("threshold_rows", index, "high_strain_fraction"),
                    f"expected {expected!r}, got {fraction!r}",
                )
        if high_count is not None and overlap_count is not None and high_count > 0:
            expected_overlap = float(overlap_count) / float(high_count)
            if abs(overlap_fraction - expected_overlap) > 1.0e-12:
                _record_error(
                    errors,
                    ("threshold_rows", index, "high_strain_boundary_overlap_fraction"),
                    f"expected {expected_overlap!r}, got {overlap_fraction!r}",
                )

        for key in ("distance_step_min", "distance_step_mean", "distance_step_median", "distance_step_max", "distance_physical_min", "distance_physical_mean", "distance_physical_median", "distance_physical_max"):
            value = row.get(key)
            if value is not None and _coerce_finite_float(value) is None:
                _record_error(errors, ("threshold_rows", index, key), "must be finite if present")
        if row.get("distance_step_min") is not None and row.get("distance_step_max") is not None:
            if row["distance_step_min"] > row["distance_step_max"]:
                _record_error(errors, ("threshold_rows", index), "distance_step_min > distance_step_max")
        if row.get("distance_step_min") is not None and row.get("distance_step_mean") is not None:
            if row["distance_step_min"] > row["distance_step_mean"] + 1.0e-12:
                _record_error(errors, ("threshold_rows", index), "distance_step_min > distance_step_mean")
        if row.get("distance_step_mean") is not None and row.get("distance_step_max") is not None:
            if row["distance_step_mean"] > row["distance_step_max"] + 1.0e-12:
                _record_error(errors, ("threshold_rows", index), "distance_step_mean > distance_step_max")

    return counts_totals, high_counts, overlap_counts


def _validate_aggregate(
    payload: dict[str, Any],
    rows: list[Any],
    band_values: list[float],
    strain_thresholds: list[float],
    shell_step_limit: int,
    band_selected_count_sum: int,
    threshold_counts: list[int],
    errors: list[str],
    warnings: list[str],
) -> None:
    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        _record_error(errors, ("aggregate",), "must be an object")
        return

    if aggregate.get("processed_frames") != len(rows):
        _record_error(errors, ("aggregate", "processed_frames"), f"expected {len(rows)!r}")

    status_counts = {
        "ok_frames": 0,
        "partial_frames": 0,
        "missing_frames": 0,
        "error_frames": 0,
    }
    expected_cell_count = 0
    expected_finite_count = 0
    for row in rows:
        if not isinstance(row, dict):
            continue
        expected_cell_count += int(row.get("cell_count", 0))
        expected_finite_count += int(row.get("finite_cell_count", 0))
        status = row.get("status")
        if status == OK_STATUS:
            status_counts["ok_frames"] += 1
        elif status == PARTIAL_STATUS:
            status_counts["partial_frames"] += 1
        elif status == MISSING_REQUIRED_STATUS:
            status_counts["missing_frames"] += 1
        else:
            status_counts["error_frames"] += 1

    for key, expected in status_counts.items():
        if aggregate.get(key) != expected:
            _record_error(errors, ("aggregate", key), f"must match computed {expected!r}")

    if _coerce_nonnegative_int(aggregate.get("global_cell_count")) != expected_cell_count:
        _record_error(errors, ("aggregate", "global_cell_count"), f"expected {expected_cell_count!r}")
    if _coerce_nonnegative_int(aggregate.get("global_finite_cell_count")) != expected_finite_count:
        _record_error(errors, ("aggregate", "global_finite_cell_count"), f"expected {expected_finite_count!r}")

    global_selected_boundary_proxy_count = 0
    aggregate_band_rows = aggregate.get("boundary_proxy", {}).get("band_rows") if isinstance(aggregate.get("boundary_proxy"), dict) else None
    if not isinstance(aggregate_band_rows, list):
        _record_error(errors, ("aggregate", "boundary_proxy", "band_rows"), "must be a list")
        aggregate_band_rows = []

    if len(aggregate_band_rows) != len(band_values):
        _record_error(errors, ("aggregate", "boundary_proxy", "band_rows"), f"must have length {len(band_values)!r}")

    previous_count = None
    selected_count_total = 0
    for index, (band, row) in enumerate(zip(band_values, aggregate_band_rows, strict=False)):
        if not isinstance(row, dict):
            _record_error(errors, ("aggregate", "boundary_proxy", "band_rows", index), "must be an object")
            continue
        if _coerce_finite_float(row.get("band")) != float(band):
            _record_error(errors, ("aggregate", "boundary_proxy", "band_rows", index, "band"), f"must be {band!r}")
        count = _coerce_nonnegative_int(row.get("count"))
        fraction = _coerce_finite_float(row.get("fraction"))
        selected_count = _coerce_nonnegative_int(row.get("selected_count"))
        selected_fraction = _coerce_finite_float(row.get("selected_fraction"))
        if count is None:
            _record_error(errors, ("aggregate", "boundary_proxy", "band_rows", index, "count"), "must be nonnegative int")
            count = 0
        if fraction is None:
            _record_error(errors, ("aggregate", "boundary_proxy", "band_rows", index, "fraction"), "must be finite")
            fraction = 0.0
        if selected_count is None:
            _record_error(errors, ("aggregate", "boundary_proxy", "band_rows", index, "selected_count"), "must be nonnegative int")
            selected_count = 0
        if selected_fraction is None:
            _record_error(errors, ("aggregate", "boundary_proxy", "band_rows", index, "selected_fraction"), "must be finite")
            selected_fraction = 0.0
        if previous_count is not None and count < previous_count:
            _record_error(errors, ("aggregate", "boundary_proxy", "band_rows", index, "count"), "counts must be nondecreasing across bands")
        previous_count = count
        if finite_count := expected_finite_count:
            expected_fraction = float(count) / float(finite_count)
            if abs(fraction - expected_fraction) > 1.0e-12:
                _record_error(
                    errors,
                    ("aggregate", "boundary_proxy", "band_rows", index, "fraction"),
                    f"expected {expected_fraction!r}, got {fraction!r}",
                )
        selected_count_total += selected_count
        if abs(selected_fraction - _coerce_nonnegative_int(row.get("selected_count")) / float(len(rows)) if len(rows) > 0 else 0.0) > 1.0e-12:
            pass

    if selected_count_total != len(rows):
        _record_error(errors, ("aggregate", "boundary_proxy", "band_rows"), f"selected_count total must equal processed_frames {len(rows)!r}")

    threshold_rows = aggregate.get("threshold_rows")
    if not isinstance(threshold_rows, list):
        _record_error(errors, ("aggregate", "threshold_rows"), "must be a list")
        return
    if len(threshold_rows) < len(strain_thresholds):
        _record_error(errors, ("aggregate", "threshold_rows"), f"must have length at least {len(strain_thresholds)!r}")

    for index, (threshold, row) in enumerate(zip(strain_thresholds, threshold_rows)):
        if not isinstance(row, dict):
            _record_error(errors, ("aggregate", "threshold_rows", index), "must be an object")
            continue
        if _coerce_finite_float(row.get("k0")) != float(threshold):
            _record_error(errors, ("aggregate", "threshold_rows", index, "k0"), f"must be {threshold!r}")
        high_count = _coerce_nonnegative_int(row.get("high_strain_count"))
        overlap_count = _coerce_nonnegative_int(row.get("high_strain_boundary_overlap_count"))
        fraction = _coerce_finite_float(row.get("high_strain_fraction"))
        overlap_fraction = _coerce_finite_float(row.get("high_strain_boundary_overlap_fraction"))
        if high_count is None:
            _record_error(errors, ("aggregate", "threshold_rows", index, "high_strain_count"), "must be nonnegative int")
            high_count = 0
        if overlap_count is None:
            _record_error(errors, ("aggregate", "threshold_rows", index, "high_strain_boundary_overlap_count"), "must be nonnegative int")
            overlap_count = 0
        if fraction is None:
            _record_error(errors, ("aggregate", "threshold_rows", index, "high_strain_fraction"), "must be finite")
            fraction = 0.0
        if overlap_fraction is None:
            _record_error(errors, ("aggregate", "threshold_rows", index, "high_strain_boundary_overlap_fraction"), "must be finite")
            overlap_fraction = 0.0
        if high_count != threshold_counts[index]:
            _record_error(errors, ("aggregate", "threshold_rows", index, "high_strain_count"), f"must match computed {threshold_counts[index]!r}")
        expected_fraction = float(high_count) / float(expected_finite_count) if expected_finite_count > 0 else 0.0
        if abs(fraction - expected_fraction) > 1.0e-12:
            _record_error(
                errors,
                ("aggregate", "threshold_rows", index, "high_strain_fraction"),
                f"expected {expected_fraction!r}, got {fraction!r}",
            )
        if high_count > 0:
            expected_overlap_fraction = float(overlap_count) / float(high_count)
        else:
            expected_overlap_fraction = 0.0
        if abs(overlap_fraction - expected_overlap_fraction) > 1.0e-12:
            _record_error(
                errors,
                ("aggregate", "threshold_rows", index, "high_strain_boundary_overlap_fraction"),
                f"expected {expected_overlap_fraction!r}, got {overlap_fraction!r}",
            )
        counts = row.get("shell_step_counts")
        fractions = row.get("shell_step_fractions")
        if not isinstance(counts, list) or len(counts) != shell_step_limit + 2:
            _record_error(errors, ("aggregate", "threshold_rows", index, "shell_step_counts"), f"must be length {shell_step_limit + 2}")
            counts = []
        if not isinstance(fractions, list) or len(fractions) != shell_step_limit + 2:
            _record_error(errors, ("aggregate", "threshold_rows", index, "shell_step_fractions"), f"must be length {shell_step_limit + 2}")
            fractions = []
        parsed_counts = []
        for bucket_index, item in enumerate(counts):
            parsed = _coerce_nonnegative_int(item)
            if parsed is None:
                _record_error(errors, ("aggregate", "threshold_rows", index, "shell_step_counts", bucket_index), "must be nonnegative int")
                parsed = 0
            parsed_counts.append(parsed)
        if parsed_counts and sum(parsed_counts) != high_count:
            _record_error(errors, ("aggregate", "threshold_rows", index, "shell_step_counts"), "must sum to high_strain_count")
        parsed_fractions = []
        for bucket_index, item in enumerate(fractions):
            parsed = _coerce_finite_float(item)
            if parsed is None:
                _record_error(errors, ("aggregate", "threshold_rows", index, "shell_step_fractions", bucket_index), "must be finite")
                parsed = 0.0
            parsed_fractions.append(parsed)
        if high_count > 0:
            expected_fractions = [float(value) / float(high_count) for value in parsed_counts]
            for bucket_index, (actual, want) in enumerate(zip(parsed_fractions, expected_fractions, strict=True)):
                if abs(actual - want) > 1.0e-12:
                    _record_error(
                        errors,
                        ("aggregate", "threshold_rows", index, "shell_step_fractions", bucket_index),
                        f"expected {want!r}, got {actual!r}",
                    )
        elif any(parsed_fractions):
            _record_error(errors, ("aggregate", "threshold_rows", index, "shell_step_fractions"), "must be all zeros for empty threshold rows")

    distance_fields = ("distance_step_min", "distance_step_mean", "distance_step_median", "distance_step_max", "distance_physical_min", "distance_physical_mean", "distance_physical_median", "distance_physical_max")
    for index, row in enumerate(threshold_rows):
        if not isinstance(row, dict):
            continue
        for key in distance_fields:
            value = row.get(key)
            if value is not None and _coerce_finite_float(value) is None:
                _record_error(errors, ("aggregate", "threshold_rows", index, key), "must be finite if present")

    if _coerce_nonnegative_int(aggregate.get("global_boundary_proxy_count")) is None:
        _record_error(errors, ("aggregate", "global_boundary_proxy_count"), "must be nonnegative int")
    if _coerce_finite_float(aggregate.get("global_boundary_proxy_fraction")) is None:
        _record_error(errors, ("aggregate", "global_boundary_proxy_fraction"), "must be finite")


def _validate(payload: dict[str, Any]) -> tuple[list[str], list[str], dict[str, Any]]:
    errors: list[str] = []
    warnings: list[str] = []

    _check_control_card(payload, errors)
    _check_contract(payload, errors)
    _check_route(payload, errors)
    _check_status(payload, errors)
    _check_authority(payload, errors)
    band_values, strain_thresholds, shell_step_limit = _check_inputs(payload, errors, warnings)

    rows = payload.get("frames")
    if not isinstance(rows, list):
        _record_error(errors, ("frames",), "must be a list")
        rows = []

    selected_band_count_sum = 0
    threshold_high_counts: list[int] = [0] * len(strain_thresholds)
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            _record_error(errors, ("frames", index), "must be an object")
            continue
        status = row.get("status")
        if status not in ALLOWED_SCAN_STATUS:
            _record_error(errors, ("frames", index, "status"), f"invalid status {status!r}")
        frame = _coerce_nonnegative_int(row.get("frame"))
        snapshot = _coerce_nonnegative_int(row.get("snapshot_index"))
        if frame is None:
            _record_error(errors, ("frames", index, "frame"), "must be nonnegative int")
        if snapshot is None:
            _record_error(errors, ("frames", index, "snapshot_index"), "must be nonnegative int")
        if _coerce_nonempty_str(row.get("source")) is None and status in {OK_STATUS, PARTIAL_STATUS}:
            _record_error(errors, ("frames", index, "source"), "must be non-empty str for ok/partial rows")
        if _coerce_finite_float(row.get("domain_length")) is None:
            _record_error(errors, ("frames", index, "domain_length"), "must be finite")
        if _coerce_finite_float(row.get("grid_spacing")) is None:
            _record_error(errors, ("frames", index, "grid_spacing"), "must be finite")
        if _coerce_nonnegative_int(row.get("cell_count")) is None:
            _record_error(errors, ("frames", index, "cell_count"), "must be nonnegative int")
        if _coerce_nonnegative_int(row.get("finite_cell_count")) is None:
            _record_error(errors, ("frames", index, "finite_cell_count"), "must be nonnegative int")
        if (
            _coerce_nonnegative_int(row.get("cell_count")) is not None
            and _coerce_nonnegative_int(row.get("finite_cell_count")) is not None
            and row["finite_cell_count"] > row["cell_count"]
        ):
            _record_error(errors, ("frames", index), "finite_cell_count cannot exceed cell_count")

        boundary_proxy = row.get("boundary_proxy")
        if not isinstance(boundary_proxy, dict):
            _record_error(errors, ("frames", index, "boundary_proxy"), "must be an object")
            continue
        if _coerce_nonempty_str(boundary_proxy.get("selection_policy")) is None:
            _record_error(errors, ("frames", index, "boundary_proxy", "selection_policy"), "must be non-empty string")
        selected_band = _coerce_finite_float(boundary_proxy.get("selected_band"))
        selected_band_index = _coerce_nonnegative_int(boundary_proxy.get("selected_band_index"))
        selected_band_count = _coerce_nonnegative_int(boundary_proxy.get("selected_band_count"))
        selected_band_fraction = _coerce_finite_float(boundary_proxy.get("selected_band_fraction"))
        if selected_band is None and status in {OK_STATUS, PARTIAL_STATUS}:
            _record_error(errors, ("frames", index, "boundary_proxy", "selected_band"), "must be finite")
        if selected_band_index is None and status in {OK_STATUS, PARTIAL_STATUS}:
            _record_error(errors, ("frames", index, "boundary_proxy", "selected_band_index"), "must be nonnegative int")
        if selected_band_count is None and status in {OK_STATUS, PARTIAL_STATUS}:
            _record_error(errors, ("frames", index, "boundary_proxy", "selected_band_count"), "must be nonnegative int")
        if selected_band_fraction is None and status in {OK_STATUS, PARTIAL_STATUS}:
            _record_error(errors, ("frames", index, "boundary_proxy", "selected_band_fraction"), "must be finite")
        if selected_band_count is not None and _coerce_nonnegative_int(row.get("finite_cell_count")) is not None:
            expected_fraction = float(selected_band_count) / float(row["finite_cell_count"]) if row["finite_cell_count"] > 0 else 0.0
            if selected_band_fraction is not None and abs(selected_band_fraction - expected_fraction) > 1.0e-12:
                _record_error(
                    errors,
                    ("frames", index, "boundary_proxy", "selected_band_fraction"),
                    f"expected {expected_fraction!r}, got {selected_band_fraction!r}",
                )
        band_rows = boundary_proxy.get("band_rows")
        selected_from_rows, selected_band_from_rows = _check_band_rows(
            band_rows,
            _coerce_nonnegative_int(row.get("finite_cell_count")) or 0,
            errors,
            warnings,
        )
        if selected_band_count is not None and selected_from_rows is not None and selected_band_count != selected_from_rows:
            _record_error(errors, ("frames", index, "boundary_proxy", "selected_band_count"), f"must match selected band row {selected_from_rows!r}")
        if selected_band is not None and selected_band_from_rows is not None and abs(selected_band - selected_band_from_rows) > 1.0e-12:
            _record_error(errors, ("frames", index, "boundary_proxy", "selected_band"), f"must match selected band row {selected_band_from_rows!r}")
        if selected_band_count is not None:
            selected_band_count_sum += selected_band_count

        threshold_rows = row.get("threshold_rows")
        counts, high_counts, overlap_counts = _check_threshold_rows(
            threshold_rows,
            shell_step_limit,
            _coerce_nonnegative_int(row.get("finite_cell_count")) or 0,
            errors,
            warnings,
        )
        if (len(threshold_rows) if isinstance(threshold_rows, list) else 0) < len(strain_thresholds):
            _record_error(errors, ("frames", index, "threshold_rows"), f"must have length at least {len(strain_thresholds)!r}")
        if len(threshold_rows) >= len(strain_thresholds):
            for threshold_index, high_count in enumerate(high_counts):
                threshold_high_counts[threshold_index] += high_count

        if status in {MISSING_REQUIRED_STATUS, ERROR_STATUS}:
            row_errors = row.get("errors")
            if row_errors is not None and not isinstance(row_errors, list):
                _record_error(errors, ("frames", index, "errors"), "must be a list if present")
            if not row_errors:
                _record_warning(warnings, ("frames", index, "errors"), "no row errors recorded")

    _validate_aggregate(
        payload,
        rows,
        band_values,
        strain_thresholds,
        shell_step_limit,
        selected_band_count_sum,
        threshold_high_counts,
        errors,
        warnings,
    )

    details = {
        "status": payload.get("status"),
        "row_count": len(rows),
        "warnings": len(warnings),
        "errors": len(errors),
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
            "route_decision": SCAN_CHECK_ROUTE,
            "input": {"scan_json": str(args.scan_json), "output_json": str(args.output_json)},
            "details": {},
            "warnings": [],
            "errors": [str(exc)],
            "changed_files": [str(args.scan_json)],
        }
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        text = _json_text(result, args.pretty) + "\n"
        args.output_json.write_text(text, encoding="utf-8")
        print(text, end="")
        return 1

    errors, warnings, details = _validate(payload)
    output_payload = {
        "contract": CONTRACT,
        **CONTROL_CARD,
        "control_card": CONTROL_CARD,
        "status": ERROR_STATUS if errors else OK_STATUS,
        "route_decision": SCAN_CHECK_ROUTE,
        "input": {"scan_json": str(args.scan_json), "output_json": str(args.output_json)},
        "details": details,
        "warnings": warnings,
        "errors": errors,
        "changed_files": [str(args.scan_json), str(args.output_json)],
    }

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    text = _json_text(output_payload, args.pretty) + "\n"
    args.output_json.write_text(text, encoding="utf-8")
    print(text, end="")
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
