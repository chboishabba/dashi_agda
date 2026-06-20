#!/usr/bin/env python3
"""Validate ns_lambda2_boundary_regularity_scan outputs."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_lambda2_boundary_regularity_scan.py"
CONTRACT = "check_ns_lambda2_boundary_regularity_scan"

SCAN_CONTRACT = "ns_lambda2_boundary_regularity_scan"
SCAN_ROUTE_DECISION = "FAIL_CLOSED_LAMBDA2_BOUNDARY_REGULARITY_SCAN"

DEFAULT_INPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_lambda2_boundary_regularity_scan_N128_20260620.json"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "check_ns_lambda2_boundary_regularity_scan_N128_20260620.json"
)

CONTROL_CARD = {
    "O": "Validate the N128 lambda2-boundary regularity proxy scan contract.",
    "R": "Check control-card fields, authority booleans, per-frame row arithmetic, and aggregate reconciliation.",
    "C": SCRIPT_NAME,
    "S": (
        "Fail-closed schema and consistency checks: malformed row shape, status/count/fraction "
        "mismatches, or aggregate mismatch are errors."
    ),
    "L": "Load scan JSON, validate metadata/rows/summary, and emit checker status JSON.",
    "P": "FAIL_CLOSED_LAMBDA2_BOUNDARY_REGULARITY_SCAN_CHECK",
    "G": "This is an empirical telemetry checker; no mathematical claim is promoted.",
    "F": "Mismatches become hard errors; degraded rows are expected when metadata fallback is triggered.",
}

OK_STATUS = "ok"
DEGRADED_STATUS = "degraded"
MISSING_REQUIRED_STATUS = "missing_required_field"
ERROR_STATUS = "error"

ALLOWED_STATUSES = {
    OK_STATUS,
    DEGRADED_STATUS,
    MISSING_REQUIRED_STATUS,
    ERROR_STATUS,
}

CHECK_CARD_KEYS = ("O", "R", "C", "S", "L", "P", "G", "F")
TOLERANCE = 1.0e-12


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--scan-json",
        type=Path,
        default=DEFAULT_INPUT,
        help="Path to ns_lambda2_boundary_regularity_scan JSON.",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Path to write check output JSON.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output.")
    return parser.parse_args()


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing scan JSON: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"scan JSON must be an object: {path}")
    return payload


def _write_json(path: Path, payload: dict[str, Any], pretty: bool) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    dump_kwargs = {
        "sort_keys": True,
        "allow_nan": False,
    }
    if pretty:
        dump_kwargs["indent"] = 2
    else:
        dump_kwargs["separators"] = (",", ":")
    path.write_text(json.dumps(payload, **dump_kwargs) + "\n", encoding="utf-8")


def _join_path(parts: tuple[Any, ...]) -> str:
    if not parts:
        return ""
    pieces: list[str] = []
    for item in parts:
        if isinstance(item, int):
            if pieces:
                pieces[-1] += f"[{item}]"
            else:
                pieces.append(f"[{item}]")
            continue
        pieces.append(str(item))
    return ".".join(pieces)


def _record_error(errors: list[str], path: tuple[Any, ...], message: str) -> None:
    prefix = _join_path(path)
    errors.append(f"{prefix}: {message}" if prefix else message)


def _record_warning(warnings: list[str], path: tuple[Any, ...], message: str) -> None:
    prefix = _join_path(path)
    warnings.append(f"{prefix}: {message}" if prefix else message)


def _coerce_finite_float(value: Any) -> float | None:
    if isinstance(value, bool) or value is None:
        return None
    try:
        value_f = float(value)
    except (TypeError, ValueError):
        return None
    return value_f if math.isfinite(value_f) else None


def _coerce_nonnegative_int(value: Any) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if isinstance(value, float) and value.is_integer():
        parsed = int(value)
        return parsed if parsed >= 0 else None
    return None


def _coerce_nonnegative_float(value: Any) -> float | None:
    value_f = _coerce_finite_float(value)
    if value_f is None or value_f < 0.0:
        return None
    return value_f


def _check_control_card(payload: dict[str, Any], errors: list[str]) -> None:
    for key in CHECK_CARD_KEYS:
        value = payload.get(key)
        if not isinstance(value, str) or not value.strip():
            _record_error(errors, (key,), "missing required control-card field")


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
    for key, required in expected.items():
        value = authority.get(key)
        if not isinstance(value, bool):
            _record_error(errors, ("authority", key), "must be bool")
        elif value is not required:
            _record_error(errors, ("authority", key), f"must be {required!r}")


def _check_inputs(payload: dict[str, Any], errors: list[str]) -> list[float]:
    inputs = payload.get("inputs")
    if not isinstance(inputs, dict):
        _record_error(errors, ("inputs",), "must be an object")
        return []
    raw = inputs.get("raw_archive")
    derived = inputs.get("derived_archive")
    frame = inputs.get("frame")
    frame_limit = inputs.get("frame_limit")
    grad_thresholds = inputs.get("gradient_thresholds")
    lambda2_band = inputs.get("lambda2_band")
    override = inputs.get("domain_length_override")

    if raw is not None and not isinstance(raw, str):
        _record_error(errors, ("inputs", "raw_archive"), "must be string or null")
    if derived is not None and not isinstance(derived, str):
        _record_error(errors, ("inputs", "derived_archive"), "must be string or null")
    if frame is not None and _coerce_nonnegative_int(frame) is None:
        _record_error(errors, ("inputs", "frame"), "must be null or nonnegative int")
    if frame_limit is None or _coerce_nonnegative_int(frame_limit) is None or frame_limit <= 0:
        _record_error(errors, ("inputs", "frame_limit"), "must be positive int")
    if _coerce_nonnegative_float(lambda2_band) is None:
        _record_error(errors, ("inputs", "lambda2_band"), "must be finite nonnegative float")

    thresholds: list[float] = []
    if not isinstance(grad_thresholds, list) or not grad_thresholds:
        _record_error(errors, ("inputs", "gradient_thresholds"), "must be a non-empty list")
        return thresholds
    for index, threshold in enumerate(grad_thresholds):
        parsed = _coerce_nonnegative_float(threshold)
        if parsed is None:
            _record_error(errors, ("inputs", "gradient_thresholds", index), "must be finite nonnegative float")
        else:
            thresholds.append(parsed)
    # Keep deterministic threshold ordering for downstream summary checks.
    thresholds = sorted(set(thresholds))

    if override is not None and _coerce_finite_float(override) is None:
        _record_error(errors, ("inputs", "domain_length_override"), "must be finite float or null")
    return thresholds


def _coerce_prob(value: Any, path: tuple[Any, ...], warnings: list[str], *, allow_none: bool = False) -> float | None:
    value_f = _coerce_finite_float(value)
    if value_f is None:
        if value is None and allow_none:
            return None
        _record_warning(warnings, path, "non-finite probability-like value")
        return None
    if not (0.0 <= value_f <= 1.0):
        _record_warning(warnings, path, "probability-like value outside [0,1]")
    return value_f


def _check_threshold_row(
    row: dict[str, Any],
    row_index: int,
    expected_thresholds: list[float],
    warnings: list[str],
    errors: list[str],
) -> dict[float, dict[str, float | int]]:
    threshold_rows = row.get("grad_threshold_rows")
    if not isinstance(threshold_rows, list):
        _record_error(errors, (row_index,), "grad_threshold_rows missing or not a list")
        return {}
    found: dict[float, dict[str, float | int]] = {}
    for index, threshold_row in enumerate(threshold_rows):
        if not isinstance(threshold_row, dict):
            _record_error(errors, (row_index, "grad_threshold_rows", index), "threshold row must be an object")
            continue
        threshold = _coerce_finite_float(threshold_row.get("threshold"))
        if threshold is None:
            _record_error(errors, (row_index, "grad_threshold_rows", index), "threshold must be finite")
            continue
        normalized = None
        for candidate in expected_thresholds:
            if math.isclose(threshold, candidate, rel_tol=0.0, abs_tol=0.0):
                normalized = candidate
                break
        if normalized is None:
            _record_warning(
                warnings,
                (row_index, "grad_threshold_rows", index),
                f"threshold {threshold} not declared in scan inputs",
            )
            normalized = threshold
        count = _coerce_nonnegative_int(threshold_row.get("count"))
        fraction_band = _coerce_prob(threshold_row.get("fraction_band"), (row_index, "grad_threshold_rows", index, "fraction_band"), warnings)
        fraction_domain = _coerce_prob(
            threshold_row.get("fraction_domain"), (row_index, "grad_threshold_rows", index, "fraction_domain"), warnings
        )
        if count is None:
            _record_error(errors, (row_index, "grad_threshold_rows", index, "count"), "count must be nonnegative int")
        if fraction_band is None:
            _record_warning(warnings, (row_index, "grad_threshold_rows", index, "fraction_band"), "missing or invalid")
        if fraction_domain is None:
            _record_warning(warnings, (row_index, "grad_threshold_rows", index, "fraction_domain"), "missing or invalid")
        found[normalized] = {"threshold": threshold, "count": count if count is not None else 0, "fraction_band": fraction_band or 0.0, "fraction_domain": fraction_domain or 0.0}
    return found


def _collect_threshold_stats(
    rows: list[dict[str, Any]],
    threshold: float,
) -> dict[str, list[float | int]]:
    count_values: list[float | int] = []
    fraction_band_values: list[float] = []
    fraction_domain_values: list[float] = []
    threshold_rows = [row.get("grad_threshold_rows") for row in rows]
    for row_entry in threshold_rows:
        if not isinstance(row_entry, list):
            continue
        found = False
        for item in row_entry:
            if not isinstance(item, dict):
                continue
            row_threshold = _coerce_finite_float(item.get("threshold"))
            if row_threshold is None:
                continue
            if not math.isclose(row_threshold, threshold, rel_tol=0.0, abs_tol=0.0):
                continue
            count = _coerce_nonnegative_int(item.get("count"))
            fraction_band = _coerce_prob(item.get("fraction_band"), (), [])
            fraction_domain = _coerce_prob(item.get("fraction_domain"), (), [])
            if count is not None:
                count_values.append(count)
            if fraction_band is not None:
                fraction_band_values.append(fraction_band)
            if fraction_domain is not None:
                fraction_domain_values.append(fraction_domain)
            found = True
            break
        if not found:
            pass
    return {
        "count": count_values,
        "fraction_band": fraction_band_values,
        "fraction_domain": fraction_domain_values,
    }


def _float_stats(values: list[float] | list[int]) -> tuple[float | None, float | None, float | None]:
    if not values:
        return None, None, None
    values_f = [float(v) for v in values]
    return (
        min(values_f),
        sum(values_f) / len(values_f),
        max(values_f),
    )


def _compare_float(value: Any, expected: float | None) -> bool:
    if value is None or expected is None:
        return value is None and expected is None
    value_f = _coerce_finite_float(value)
    if value_f is None:
        return False
    return abs(value_f - expected) <= TOLERANCE * max(1.0, abs(expected))


def _check_rows(
    payload: dict[str, Any],
    expected_thresholds: list[float],
    warnings: list[str],
    errors: list[str],
) -> tuple[list[dict[str, Any]], list[float]]:
    rows_value = payload.get("rows")
    if not isinstance(rows_value, list):
        _record_error(errors, ("rows",), "must be a list")
        return [], []

    rows: list[dict[str, Any]] = []
    threshold_set: set[float] = set()
    for index, row in enumerate(rows_value):
        if not isinstance(row, dict):
            _record_error(errors, (index,), "row must be an object")
            continue
        rows.append(row)
        status = row.get("status")
        if status not in ALLOWED_STATUSES:
            _record_error(errors, (index, "status"), f"must be one of {sorted(ALLOWED_STATUSES)!r}, got {status!r}")
            continue

        frame = _coerce_nonnegative_int(row.get("frame"))
        if frame is None:
            _record_error(errors, (index, "frame"), "must be nonnegative int")
        snapshot = _coerce_nonnegative_int(row.get("snapshot"))
        if snapshot is None:
            _record_error(errors, (index, "snapshot"), "must be nonnegative int")
        if not isinstance(row.get("source_path"), str):
            _record_warning(warnings, (index, "source_path"), "source_path should be string")
        if not isinstance(row.get("source_type"), str):
            _record_warning(warnings, (index, "source_type"), "source_type should be string")

        if status == ERROR_STATUS:
            errors_list = row.get("errors")
            if not isinstance(errors_list, list) or not errors_list:
                _record_error(errors, (index, "errors"), "error rows must have non-empty errors list")
            continue
        if status == MISSING_REQUIRED_STATUS:
            if not isinstance(row.get("errors"), list):
                _record_error(errors, (index, "errors"), "missing_required rows require errors list")
            continue

        cell_count = _coerce_nonnegative_int(row.get("cell_count"))
        finite_cell_count = _coerce_nonnegative_int(row.get("finite_cell_count"))
        band_cell_count = _coerce_nonnegative_int(row.get("band_cell_count"))
        if cell_count is None:
            _record_error(errors, (index, "cell_count"), "must be nonnegative int")
        if finite_cell_count is None:
            _record_error(errors, (index, "finite_cell_count"), "must be nonnegative int")
        if band_cell_count is None:
            _record_error(errors, (index, "band_cell_count"), "must be nonnegative int")
        if finite_cell_count is not None and cell_count is not None and finite_cell_count > cell_count:
            _record_error(errors, (index,), "finite_cell_count cannot exceed cell_count")
        if band_cell_count is not None and finite_cell_count is not None and band_cell_count > finite_cell_count:
            _record_error(errors, (index,), "band_cell_count cannot exceed finite_cell_count")

        fraction = _coerce_prob(row.get("band_cell_fraction"), (index, "band_cell_fraction"), warnings, allow_none=True)
        if (
            fraction is not None
            and band_cell_count is not None
            and finite_cell_count not in (None, 0)
            and finite_cell_count > 0
        ):
            expected_fraction = band_cell_count / float(finite_cell_count)
            if abs(fraction - expected_fraction) > 1.0e-10:
                _record_warning(warnings, (index, "band_cell_fraction"), "fraction mismatch with band_cell_count/finite_cell_count")

        grad_stats = row.get("grad_lambda2_stats")
        if not isinstance(grad_stats, dict):
            _record_error(errors, (index, "grad_lambda2_stats"), "must be a dict")
        else:
            for key in ("min", "mean", "max"):
                if key in grad_stats:
                    value = _coerce_finite_float(grad_stats.get(key))
                    if value is None and grad_stats.get(key) is not None:
                        _record_error(errors, (index, "grad_lambda2_stats", key), "must be finite or null")
        band_grad_stats = row.get("band_grad_stats")
        if not isinstance(band_grad_stats, dict):
            _record_error(errors, (index, "band_grad_stats"), "must be a dict")
        else:
            for key in ("min", "mean", "max"):
                if key in band_grad_stats:
                    value = _coerce_finite_float(band_grad_stats.get(key))
                    if value is None and band_grad_stats.get(key) is not None:
                        _record_error(errors, (index, "band_grad_stats", key), "must be finite or null")

        threshold_map = _check_threshold_row(row, index, expected_thresholds, warnings, errors)
        for threshold in expected_thresholds:
            if threshold not in threshold_map:
                _record_warning(
                    warnings,
                    (index, "grad_threshold_rows"),
                    f"missing declared threshold {threshold}",
                )
        for threshold_key, threshold_payload in threshold_map.items():
            count = threshold_payload.get("count")
            if not isinstance(count, int):
                continue
            if band_cell_count is not None and count > band_cell_count:
                _record_error(
                    errors,
                    (index, "grad_threshold_rows", threshold_key),
                    f"threshold count {count} exceeds band_cell_count {band_cell_count}",
                )
            if finite_cell_count not in (None, 0) and finite_cell_count > 0 and band_cell_count is not None:
                observed_fraction_domain = threshold_payload.get("fraction_domain")
                if isinstance(observed_fraction_domain, (float, int)):
                    expected_fraction_domain = count / float(finite_cell_count)
                    if abs(observed_fraction_domain - expected_fraction_domain) > 1.0e-10:
                        _record_warning(
                            warnings,
                            (index, "grad_threshold_rows", threshold_key),
                            f"threshold fraction_domain mismatch: expected {expected_fraction_domain}, got {observed_fraction_domain}",
                        )
            if finite_cell_count not in (None, 0) and band_cell_count not in (None, 0):
                observed_fraction_band = threshold_payload.get("fraction_band")
                if isinstance(observed_fraction_band, (float, int)):
                    expected_fraction_band = count / float(band_cell_count)
                    if abs(observed_fraction_band - expected_fraction_band) > 1.0e-10:
                        _record_warning(
                            warnings,
                            (index, "grad_threshold_rows", threshold_key),
                            f"threshold fraction_band mismatch: expected {expected_fraction_band}, got {observed_fraction_band}",
                        )
        for threshold in threshold_map:
            threshold_set.add(float(threshold))

    return rows, sorted(threshold_set)


def _validate_summary(payload: dict[str, Any], warnings: list[str], errors: list[str], rows: list[dict[str, Any]]) -> list[float]:
    summary = payload.get("summary")
    if not isinstance(summary, dict):
        _record_error(errors, ("summary",), "must be an object")
        return []

    requested_limit = _coerce_nonnegative_int(summary.get("requested_frame_limit"))
    if requested_limit is None:
        _record_error(errors, ("summary", "requested_frame_limit"), "must be nonnegative int")
    processed = _coerce_nonnegative_int(summary.get("processed_frame_count"))
    if processed is None:
        _record_error(errors, ("summary", "processed_frame_count"), "must be nonnegative int")
    elif processed != len(rows):
        _record_error(errors, ("summary", "processed_frame_count"), f"must equal len(rows)={len(rows)}")

    ok_frames = _coerce_nonnegative_int(summary.get("ok_frame_count")) or 0
    degraded_frames = _coerce_nonnegative_int(summary.get("degraded_frame_count")) or 0
    missing_frames = _coerce_nonnegative_int(summary.get("missing_frame_count")) or 0
    error_frames = _coerce_nonnegative_int(summary.get("error_frame_count")) or 0

    status_counts = summary.get("status_counts")
    if not isinstance(status_counts, dict):
        _record_error(errors, ("summary", "status_counts"), "must be an object")
    else:
        if ok_frames != sum(1 for row in rows if row.get("status") == OK_STATUS):
            _record_error(errors, ("summary", "ok_frame_count"), "mismatch with row statuses")
        if degraded_frames != sum(1 for row in rows if row.get("status") == DEGRADED_STATUS):
            _record_error(errors, ("summary", "degraded_frame_count"), "mismatch with row statuses")
        if missing_frames != sum(1 for row in rows if row.get("status") == MISSING_REQUIRED_STATUS):
            _record_error(errors, ("summary", "missing_frame_count"), "mismatch with row statuses")
        if error_frames != sum(1 for row in rows if row.get("status") == ERROR_STATUS):
            _record_error(errors, ("summary", "error_frame_count"), "mismatch with row statuses")
        for key, expected_count in {
            OK_STATUS: ok_frames,
            DEGRADED_STATUS: degraded_frames,
            MISSING_REQUIRED_STATUS: missing_frames,
            ERROR_STATUS: error_frames,
        }.items():
            actual = status_counts.get(key)
            if isinstance(actual, int):
                if int(actual) != int(expected_count):
                    _record_error(errors, ("summary", "status_counts", key), "mismatch with frame status")

    thresholds: list[float] = []
    for raw_key in summary.get("threshold_summary", {}).keys():
        if not isinstance(raw_key, str):
            _record_error(errors, ("summary", "threshold_summary"), f"threshold key must be string, got {raw_key!r}")
            continue
        try:
            thresholds.append(float(raw_key))
        except ValueError:
            _record_error(errors, ("summary", "threshold_summary", raw_key), "threshold key must parse as float")
    return thresholds


def _validate_threshold_summary(
    payload: dict[str, Any],
    rows: list[dict[str, Any]],
    thresholds: list[float],
    warnings: list[str],
    errors: list[str],
) -> None:
    summary = payload.get("summary")
    if not isinstance(summary, dict):
        return
    threshold_summary = summary.get("threshold_summary")
    if not isinstance(threshold_summary, dict):
        _record_error(errors, ("summary", "threshold_summary"), "must be an object")
        return
    for threshold in thresholds:
        row_key = str(threshold)
        entry = threshold_summary.get(row_key)
        if not isinstance(entry, dict):
            _record_error(errors, ("summary", "threshold_summary", row_key), "missing threshold summary entry")
            continue
        usable_rows = [row for row in rows if row.get("status") in (OK_STATUS, DEGRADED_STATUS)]
        stats = _collect_threshold_stats(usable_rows, threshold)
        count_values = stats["count"]
        frac_band_values = stats["fraction_band"]
        frac_dom_values = stats["fraction_domain"]

        expected = {
            "count_stats": _float_stats(count_values),
            "fraction_band_stats": _float_stats(frac_band_values),
            "fraction_domain_stats": _float_stats(frac_dom_values),
        }
        for section, values in expected.items():
            section_payload = entry.get(section)
            if not isinstance(section_payload, dict):
                _record_error(
                    errors,
                    ("summary", "threshold_summary", row_key, section),
                    "section must be an object",
                )
                continue
            observed_count = _coerce_nonnegative_int(section_payload.get("frame_count")) or 0
            if section == "count_stats":
                sample_values = count_values
            elif section == "fraction_band_stats":
                sample_values = frac_band_values
            else:
                sample_values = frac_dom_values
            expected_count = len(sample_values)
            if observed_count != expected_count:
                _record_error(
                    errors,
                    ("summary", "threshold_summary", row_key, section, "frame_count"),
                    f"expected {expected_count}, got {observed_count}",
                )
            observed_min = section_payload.get("min")
            observed_mean = section_payload.get("mean")
            observed_max = section_payload.get("max")
            expected_min, expected_mean, expected_max = (
                expected[section][0],
                expected[section][1],
                expected[section][2],
            )
            if not _compare_float(observed_min, expected_min):
                _record_warning(warnings, ("summary", "threshold_summary", row_key, section, "min"), "min mismatch")
            if not _compare_float(observed_mean, expected_mean):
                _record_warning(warnings, ("summary", "threshold_summary", row_key, section, "mean"), "mean mismatch")
            if not _compare_float(observed_max, expected_max):
                _record_warning(warnings, ("summary", "threshold_summary", row_key, section, "max"), "max mismatch")


def _validate_payload(payload: dict[str, Any]) -> tuple[list[str], list[str], dict[str, Any], list[float]]:
    errors: list[str] = []
    warnings: list[str] = []

    if payload.get("contract") != SCAN_CONTRACT:
        _record_error(errors, ("contract",), f"must be {SCAN_CONTRACT!r}")
    if payload.get("route_decision") != SCAN_ROUTE_DECISION:
        _record_error(errors, ("route_decision",), f"must be {SCAN_ROUTE_DECISION!r}")

    status = payload.get("status")
    if not isinstance(status, str):
        _record_error(errors, ("status",), "must be a string")

    _check_control_card(payload, errors)
    _check_authority(payload, errors)

    thresholds = _check_inputs(payload, errors)
    rows, seen_thresholds = _check_rows(payload, thresholds, warnings, errors)
    _validate_summary(payload, warnings, errors, rows)
    _validate_threshold_summary(payload, rows, thresholds if thresholds else seen_thresholds, warnings, errors)

    if status not in ALLOWED_STATUSES:
        _record_error(errors, ("status",), f"must be one of {sorted(ALLOWED_STATUSES)!r}")
    else:
        row_statuses = {row.get("status") for row in rows if isinstance(row, dict)}
        expected = OK_STATUS
        if ERROR_STATUS in row_statuses:
            expected = ERROR_STATUS
        elif MISSING_REQUIRED_STATUS in row_statuses:
            expected = MISSING_REQUIRED_STATUS
        elif DEGRADED_STATUS in row_statuses:
            expected = DEGRADED_STATUS
        if row_statuses and status != expected:
            _record_error(errors, ("status",), f"expected {expected!r} from row statuses, got {status!r}")

    all_frames_ok_or_degraded = payload.get("summary", {}).get("all_frames_ok_or_degraded")
    if rows and isinstance(all_frames_ok_or_degraded, bool):
        expected = all(row.get("status") in (OK_STATUS, DEGRADED_STATUS) for row in rows)
        if expected != all_frames_ok_or_degraded:
            _record_warning(warnings, ("summary", "all_frames_ok_or_degraded"), "flag mismatch with row statuses")
    elif rows and all_frames_ok_or_degraded is not None and all_frames_ok_or_degraded not in (True, False):
        _record_error(errors, ("summary", "all_frames_ok_or_degraded"), "must be boolean")

    details = {
        "row_count": len(rows),
        "status_counts": {status: sum(1 for row in rows if row.get("status") == status) for status in sorted(ALLOWED_STATUSES)},
        "threshold_count": len(thresholds),
        "warn_count": len(warnings),
        "error_count": len(errors),
    }
    return errors, sorted(set(warnings)), details, thresholds


def main() -> int:
    args = _parse_args()
    try:
        payload = _load_json(args.scan_json)
    except (FileNotFoundError, json.JSONDecodeError, ValueError) as exc:
        result = {
            "contract": CONTRACT,
            "status": ERROR_STATUS,
            "errors": [str(exc)],
            "warnings": [],
            "input": {"scan_json": str(args.scan_json), "output_json": str(args.output_json)},
            "changed_files": [str(args.output_json)],
            "details": {"row_count": 0},
            **CONTROL_CARD,
            "control_card": CONTROL_CARD,
        }
        _write_json(args.output_json, result, args.pretty)
        print(json.dumps(result, sort_keys=True, indent=2 if args.pretty else None, allow_nan=False))
        return 1

    errors, warnings, details, _ = _validate_payload(payload)
    result_status = ERROR_STATUS if errors else OK_STATUS
    result = {
        "contract": CONTRACT,
        "status": result_status,
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
    return 1 if result_status != OK_STATUS else 0


if __name__ == "__main__":
    raise SystemExit(main())
