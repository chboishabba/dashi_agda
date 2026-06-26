#!/usr/bin/env python3
"""Regression checker for NS pressure/sign-convention diagnostics."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_pressure_convention_regression.py"
CONTRACT = "check_ns_pressure_convention_regression"
OK_STATUS = "ok"
ERROR_STATUS = "error"

SIGN_CONTRACT = "ns_pressure_poisson_sign_timeseries_audit"
COMPARE_CONTRACT = "ns_raw_derived_tensor_convention_compare"
BUDGET_CONTRACT = "ns_interior_budget_timeseries_diagnostic"

CHECK_CARD_KEYS = ("O", "R", "C", "S", "L", "P", "G", "F")
ALLOWED_AUTHORITY_TRUE_KEYS = {
    "candidate_only",
    "diagnostic_only",
    "empirical_non_promoting",
    "non_promoting",
}

SIGN_COUNT_KEYS = ("minus", "plus")
SIGN_SCALE_STATS_KEYS = ("min", "mean", "median", "max", "std")

COMPARE_FIELD_KEYS = ("lambda2", "g12", "lambda3")
COMPARE_CELL_RAW_KEYS = ("lambda1", "lambda2", "lambda3", "g12", "omega_norm_sq")
COMPARE_CELL_OPTIONAL_KEYS = ("lambda2", "g12", "lambda3")

BUDGET_ROW_KEYS = (
    "lambda1",
    "lambda2",
    "lambda3",
    "omega_norm_sq",
    "extensional_gain",
    "middle_damping",
    "compressive_abs_gain",
    "signed_budget",
    "omega_l3_domain_norm",
)
BUDGET_AGG_KEYS = BUDGET_ROW_KEYS + ("pressure_laplacian",)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--sign-timeseries-json",
        type=Path,
        default=None,
        help="Path to ns_pressure_poisson_sign_timeseries_audit JSON.",
    )
    parser.add_argument(
        "--raw-derived-json",
        type=Path,
        default=None,
        help="Path to ns_raw_derived_tensor_convention_compare JSON.",
    )
    parser.add_argument(
        "--budget-timeseries-json",
        type=Path,
        default=None,
        help="Path to ns_interior_budget_timeseries_diagnostic JSON.",
    )
    parser.add_argument(
        "--pretty",
        action="store_true",
        help="Pretty-print the deterministic JSON result.",
    )
    return parser.parse_args()


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing input file: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"top-level JSON payload is not an object: {path}")
    return payload


def _normalize_key(value: str) -> str:
    return "".join(character.lower() for character in value if character.isalnum())


def _join_path(path: tuple[Any, ...]) -> str:
    if not path:
        return ""
    label = ""
    for key in path:
        if isinstance(key, int):
            label += f"[{key}]"
        else:
            if label:
                label += "."
            label += str(key)
    return label


def _append_error(errors: list[str], path: tuple[Any, ...], message: str) -> None:
    label = _join_path(path)
    errors.append(f"{label}: {message}" if label else message)


def _append_warning(warnings: list[str], path: tuple[Any, ...], message: str) -> None:
    label = _join_path(path)
    warnings.append(f"{label}: {message}" if label else message)


def _is_finite_number(value: Any) -> bool:
    if isinstance(value, bool):
        return False
    if isinstance(value, int):
        return True
    if isinstance(value, float):
        return math.isfinite(value)
    return False


def _coerce_number(
    errors: list[str],
    path: tuple[Any, ...],
    value: Any,
    *,
    allow_none: bool = False,
) -> float | None:
    if value is None:
        if allow_none:
            return None
        _append_error(errors, path, "must be finite numeric, got None")
        return None
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        _append_error(errors, path, f"must be finite numeric, got {type(value).__name__}")
        return None
    value_f = float(value)
    if not math.isfinite(value_f):
        _append_error(errors, path, f"must be finite numeric, got {value!r}")
        return None
    return value_f


def _check_control_card(payload: dict[str, Any], errors: list[str], source: tuple[Any, ...]) -> None:
    for key in CHECK_CARD_KEYS:
        value = payload.get(key)
        if not isinstance(value, str) or not value.strip():
            _append_error(errors, source + (key,), "must be a non-empty string")


def _check_contract(payload: dict[str, Any], expected: str, errors: list[str], source: tuple[Any, ...]) -> None:
    contract = payload.get("contract")
    if not isinstance(contract, str) or not contract.strip():
        _append_error(errors, source + ("contract",), "must be a non-empty string")
        return
    if contract != expected:
        _append_error(errors, source + ("contract",), f"mismatch: {contract!r} (expected {expected!r})")


def _check_status(payload: dict[str, Any], errors: list[str], source: tuple[Any, ...]) -> None:
    status = payload.get("status")
    if status != OK_STATUS:
        _append_error(errors, source + ("status",), f"must be {OK_STATUS!r}, got {status!r}")


def _check_authority(payload: dict[str, Any], errors: list[str], source: tuple[Any, ...]) -> None:
    authority = payload.get("authority")
    if not isinstance(authority, dict):
        _append_error(errors, source + ("authority",), "must be an object")
        return
    if not authority:
        _append_error(errors, source + ("authority",), "must not be empty")
        return

    saw_non_promoting = False
    saw_candidate_only = False

    for key, value in sorted(authority.items(), key=lambda item: str(item[0])):
        key_text = str(key)
        normalized = _normalize_key(key_text)
        if not isinstance(value, bool):
            _append_error(errors, source + ("authority", key_text), f"must be bool, got {type(value).__name__}")
            continue
        if normalized == "candidateonly":
            saw_candidate_only = True
            if not value:
                _append_error(errors, source + ("authority", key_text), "must be true")
            continue
        if normalized in {"empiricalnonpromoting", "nonpromoting"}:
            saw_non_promoting = True
            if not value:
                _append_error(errors, source + ("authority", key_text), "must be true")
            continue
        if value and ("promotion" in normalized or "promoting" in normalized or "promoted" in normalized):
            _append_error(errors, source + ("authority", key_text), "must be false")
        elif "promotion" in normalized or "promoting" in normalized or "promoted" in normalized:
            pass
        elif value:
            _append_error(errors, source + ("authority", key_text), "unexpected true flag")

    if not saw_candidate_only:
        _append_error(errors, source + ("authority",), "missing candidate_only flag")
    if not saw_non_promoting:
        _append_error(errors, source + ("authority",), "missing empirical_non_promoting/non_promoting flag")


def _check_no_forbidden_promotion_flags(node: Any, errors: list[str], path: tuple[Any, ...]) -> None:
    if isinstance(node, dict):
        for key, value in node.items():
            if isinstance(key, str):
                normalized = _normalize_key(key)
                if (
                    ("promotion" in normalized or "promoting" in normalized or "promoted" in normalized)
                    and normalized not in {"candidateonly", "empiricalnonpromoting", "nonpromoting", "diagnosticonly"}
                    and isinstance(value, bool)
                    and value
                ):
                    _append_error(errors, path + (key,), "must be false")
            _check_no_forbidden_promotion_flags(value, errors, path + (key,))
    elif isinstance(node, list):
        for index, value in enumerate(node):
            _check_no_forbidden_promotion_flags(value, errors, path + (index,))


def _check_finite_tree(node: Any, errors: list[str], path: tuple[Any, ...]) -> None:
    if isinstance(node, dict):
        for key, value in node.items():
            _check_finite_tree(value, errors, path + (key,))
        return
    if isinstance(node, list):
        for index, value in enumerate(node):
            _check_finite_tree(value, errors, path + (index,))
        return
    if isinstance(node, bool) or node is None or isinstance(node, str):
        return
    if isinstance(node, (int, float)):
        if not _is_finite_number(node):
            _append_error(errors, path, f"must be finite numeric, got {node!r}")


def _validate_stats(
    payload: dict[str, Any],
    errors: list[str],
    path: tuple[Any, ...],
    *,
    allow_none_fields: set[str] | None = None,
    require_max_ge_min: bool = True,
) -> None:
    allow_none_fields = allow_none_fields or set()
    min_value = None
    max_value = None
    mean_value = None
    for key, value in payload.items():
        if key in allow_none_fields and value is None:
            continue
        value_f = _coerce_number(errors, path + (key,), value, allow_none=key in allow_none_fields)
        if value_f is None and value is None and key in allow_none_fields:
            continue
        if key == "min":
            min_value = value_f
        elif key == "max":
            max_value = value_f
        elif key == "mean":
            mean_value = value_f
    if require_max_ge_min and min_value is not None and max_value is not None and max_value < min_value:
        _append_error(errors, path, f"max {max_value!r} must be >= min {min_value!r}")
    if min_value is not None and mean_value is not None and mean_value < min_value:
        _append_error(errors, path, f"mean {mean_value!r} must be >= min {min_value!r}")
    if max_value is not None and mean_value is not None and mean_value > max_value:
        _append_error(errors, path, f"mean {mean_value!r} must be <= max {max_value!r}")


def _validate_sign_stats(stats: dict[str, Any], errors: list[str], path: tuple[Any, ...]) -> None:
    _validate_stats(stats, errors, path)


def _validate_sign_row(row: dict[str, Any], errors: list[str], path: tuple[Any, ...]) -> None:
    if row.get("status") != OK_STATUS:
        _append_error(errors, path + ("status",), f"must be {OK_STATUS!r}")
    frame = row.get("frame")
    if not isinstance(frame, int) or isinstance(frame, bool) or frame < 0:
        _append_error(errors, path + ("frame",), f"must be a nonnegative integer, got {frame!r}")
    best = row.get("best_sign_proxy")
    if not isinstance(best, dict):
        _append_error(errors, path + ("best_sign_proxy",), "must be an object")
        return

    for key in ("sign", "candidate"):
        value = best.get(key)
        if not isinstance(value, str) or not value.strip():
            _append_error(errors, path + ("best_sign_proxy", key), "must be a non-empty string")
    candidate = best.get("candidate")
    if isinstance(candidate, str) and candidate not in {"+Delta p", "-Delta p"}:
        _append_error(errors, path + ("best_sign_proxy", "candidate"), "must be '+Delta p' or '-Delta p'")

    sign_factor = _coerce_number(errors, path + ("best_sign_proxy", "sign_factor"), best.get("sign_factor"))
    if sign_factor is not None and sign_factor not in (-1.0, 1.0):
        _append_error(errors, path + ("best_sign_proxy", "sign_factor"), "must be -1 or 1")

    best_scale = _coerce_number(errors, path + ("best_sign_proxy", "best_scale"), best.get("best_scale"))
    if best_scale is not None and best_scale <= 0.0:
        _append_error(errors, path + ("best_sign_proxy", "best_scale"), "must be positive")

    for key in ("raw_rmse", "scaled_rmse"):
        value = _coerce_number(errors, path + ("best_sign_proxy", key), best.get(key))
        if value is not None and value < 0.0:
            _append_error(errors, path + ("best_sign_proxy", key), "must be nonnegative")

    for key in ("raw_correlation", "scaled_correlation"):
        value = best.get(key)
        if value is None:
            continue
        corr = _coerce_number(errors, path + ("best_sign_proxy", key), value)
        if corr is not None and abs(corr) > 1.0 + 1.0e-12:
            _append_error(errors, path + ("best_sign_proxy", key), "must lie in [-1, 1]")

    if isinstance(best.get("raw_rmse"), (int, float)) and isinstance(best.get("scaled_rmse"), (int, float)):
        if float(best["scaled_rmse"]) > float(best["raw_rmse"]) + 1.0e-12:
            _append_error(
                errors,
                path + ("best_sign_proxy",),
                "scaled_rmse must not exceed raw_rmse",
            )

    comparisons = row.get("comparisons")
    if not isinstance(comparisons, list) or len(comparisons) != 2:
        _append_error(errors, path + ("comparisons",), "must be a two-item list")
    else:
        seen_signs: set[str] = set()
        for index, item in enumerate(comparisons):
            if not isinstance(item, dict):
                _append_error(errors, path + ("comparisons", index), "must be an object")
                continue
            sign = item.get("sign")
            if not isinstance(sign, str) or sign not in {"plus", "minus"}:
                _append_error(errors, path + ("comparisons", index, "sign"), "must be 'plus' or 'minus'")
            else:
                seen_signs.add(sign)
            item_scale = _coerce_number(errors, path + ("comparisons", index, "best_scale"), item.get("best_scale"))
            if item_scale is not None and item_scale < 0.0:
                _append_error(errors, path + ("comparisons", index, "best_scale"), "must be nonnegative")
            for key in ("raw_rmse", "scaled_rmse"):
                value = _coerce_number(errors, path + ("comparisons", index, key), item.get(key))
                if value is not None and value < 0.0:
                    _append_error(errors, path + ("comparisons", index, key), "must be nonnegative")
            corr = item.get("raw_correlation")
            if corr is not None:
                corr_value = _coerce_number(errors, path + ("comparisons", index, "raw_correlation"), corr)
                if corr_value is not None and abs(corr_value) > 1.0 + 1.0e-12:
                    _append_error(errors, path + ("comparisons", index, "raw_correlation"), "must lie in [-1, 1]")
            corr = item.get("scaled_correlation")
            if corr is not None:
                corr_value = _coerce_number(errors, path + ("comparisons", index, "scaled_correlation"), corr)
                if corr_value is not None and abs(corr_value) > 1.0 + 1.0e-12:
                    _append_error(errors, path + ("comparisons", index, "scaled_correlation"), "must lie in [-1, 1]")
        if seen_signs != {"plus", "minus"}:
            _append_error(errors, path + ("comparisons",), "must include both plus and minus rows")

    spectral_delta = row.get("spectral_delta_p")
    spectral_negative = row.get("spectral_negative_delta_p")
    if isinstance(spectral_delta, dict):
        _validate_stats(spectral_delta, errors, path + ("spectral_delta_p",))
    else:
        _append_error(errors, path + ("spectral_delta_p",), "must be an object")
    if isinstance(spectral_negative, dict):
        _validate_stats(spectral_negative, errors, path + ("spectral_negative_delta_p",))
    else:
        _append_error(errors, path + ("spectral_negative_delta_p",), "must be an object")

    if isinstance(best.get("sign"), str) and isinstance(best.get("sign_factor"), (int, float)):
        sign = best["sign"]
        sign_factor = float(best["sign_factor"])
        if sign == "plus" and sign_factor != 1.0:
            _append_error(errors, path + ("best_sign_proxy", "sign_factor"), "must be 1 for plus")
        if sign == "minus" and sign_factor != -1.0:
            _append_error(errors, path + ("best_sign_proxy", "sign_factor"), "must be -1 for minus")


def _validate_sign_payload(payload: dict[str, Any], path: Path) -> tuple[list[str], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []
    source = ("sign",)

    _check_contract(payload, SIGN_CONTRACT, errors, source)
    _check_status(payload, errors, source)
    _check_control_card(payload, errors, source)
    _check_authority(payload, errors, source)
    _check_no_forbidden_promotion_flags(payload, errors, ())

    for key in ("frame_count", "selected_frame_count"):
        value = payload.get(key)
        if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
            _append_error(errors, source + (key,), f"must be a positive integer, got {value!r}")

    selected_frames = payload.get("selected_frames")
    if not isinstance(selected_frames, list) or not selected_frames:
        _append_error(errors, source + ("selected_frames",), "must be a non-empty list")
    else:
        for index, value in enumerate(selected_frames):
            if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                _append_error(
                    errors,
                    source + ("selected_frames", index),
                    f"must be a nonnegative integer, got {value!r}",
                )
        if isinstance(payload.get("selected_frame_count"), int) and not isinstance(payload.get("selected_frame_count"), bool):
            if payload["selected_frame_count"] != len(selected_frames):
                _append_error(
                    errors,
                    source + ("selected_frame_count",),
                    "must match selected_frames length",
                )

    rows = payload.get("rows")
    if not isinstance(rows, list) or not rows:
        _append_error(errors, source + ("rows",), "must be a non-empty list")
    else:
        for index, row in enumerate(rows):
            if not isinstance(row, dict):
                _append_error(errors, source + ("rows", index), "must be an object")
                continue
            _validate_sign_row(row, errors, source + ("rows", index))

    aggregate_counts = payload.get("aggregate_counts")
    if not isinstance(aggregate_counts, dict):
        _append_error(errors, source + ("aggregate_counts",), "must be an object")
    else:
        for key in ("selected_frame_count", "valid_frame_count", "minus_best_count", "plus_best_count"):
            value = aggregate_counts.get(key)
            if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                _append_error(
                    errors,
                    source + ("aggregate_counts", key),
                    f"must be a nonnegative integer, got {value!r}",
                )

    aggregate_metrics = payload.get("aggregate_metrics")
    if not isinstance(aggregate_metrics, dict):
        _append_error(errors, source + ("aggregate_metrics",), "must be an object")
    else:
        best_sign_counts = aggregate_metrics.get("best_sign_counts")
        if not isinstance(best_sign_counts, dict):
            _append_error(errors, source + ("aggregate_metrics", "best_sign_counts"), "must be an object")
        else:
            minus = best_sign_counts.get("minus")
            plus = best_sign_counts.get("plus")
            if not isinstance(minus, int) or isinstance(minus, bool) or minus < 0:
                _append_error(errors, source + ("aggregate_metrics", "best_sign_counts", "minus"), "must be a nonnegative integer")
            if not isinstance(plus, int) or isinstance(plus, bool) or plus < 0:
                _append_error(errors, source + ("aggregate_metrics", "best_sign_counts", "plus"), "must be a nonnegative integer")
            if isinstance(minus, int) and isinstance(plus, int) and not isinstance(minus, bool) and not isinstance(plus, bool):
                valid_rows = aggregate_counts.get("valid_frame_count") if isinstance(aggregate_counts, dict) else None
                if isinstance(valid_rows, int) and minus + plus != valid_rows:
                    _append_error(
                        errors,
                        source + ("aggregate_metrics", "best_sign_counts"),
                        "minus plus must equal valid_frame_count",
                    )

        best_sign_fraction = aggregate_metrics.get("best_sign_fraction")
        if not isinstance(best_sign_fraction, dict):
            _append_error(errors, source + ("aggregate_metrics", "best_sign_fraction"), "must be an object")
        else:
            minus_frac = best_sign_fraction.get("minus")
            plus_frac = best_sign_fraction.get("plus")
            if minus_frac is not None:
                minus_frac_f = _coerce_number(errors, source + ("aggregate_metrics", "best_sign_fraction", "minus"), minus_frac)
                if minus_frac_f is not None and not (0.0 <= minus_frac_f <= 1.0):
                    _append_error(errors, source + ("aggregate_metrics", "best_sign_fraction", "minus"), "must lie in [0, 1]")
            if plus_frac is not None:
                plus_frac_f = _coerce_number(errors, source + ("aggregate_metrics", "best_sign_fraction", "plus"), plus_frac)
                if plus_frac_f is not None and not (0.0 <= plus_frac_f <= 1.0):
                    _append_error(errors, source + ("aggregate_metrics", "best_sign_fraction", "plus"), "must lie in [0, 1]")
            if isinstance(minus_frac, (int, float)) and isinstance(plus_frac, (int, float)):
                if abs((float(minus_frac) + float(plus_frac)) - 1.0) > 1.0e-12:
                    _append_error(errors, source + ("aggregate_metrics", "best_sign_fraction"), "fractions must sum to 1")

        for key in ("best_scale_stats", "raw_rmse_stats", "scaled_rmse_stats", "raw_correlation_stats", "scaled_correlation_stats"):
            stats = aggregate_metrics.get(key)
            if not isinstance(stats, dict):
                _append_error(errors, source + ("aggregate_metrics", key), "must be an object")
                continue
            _validate_stats(stats, errors, source + ("aggregate_metrics", key))
            if key == "best_scale_stats":
                min_value = stats.get("min")
                if isinstance(min_value, (int, float)) and float(min_value) <= 0.0:
                    _append_error(errors, source + ("aggregate_metrics", key, "min"), "must be positive")
            if key in {"raw_rmse_stats", "scaled_rmse_stats"}:
                min_value = stats.get("min")
                if isinstance(min_value, (int, float)) and float(min_value) < 0.0:
                    _append_error(errors, source + ("aggregate_metrics", key, "min"), "must be nonnegative")

    sign_stability = payload.get("sign_stability")
    if not isinstance(sign_stability, dict):
        _append_error(errors, source + ("sign_stability",), "must be an object")
    else:
        modal_sign = sign_stability.get("modal_sign")
        if modal_sign is not None and (not isinstance(modal_sign, str) or modal_sign not in {"plus", "minus"}):
            _append_error(errors, source + ("sign_stability", "modal_sign"), "must be 'plus', 'minus', or null")
        modal_count = sign_stability.get("modal_count")
        if not isinstance(modal_count, int) or isinstance(modal_count, bool) or modal_count < 0:
            _append_error(errors, source + ("sign_stability", "modal_count"), "must be a nonnegative integer")
        modal_fraction = sign_stability.get("modal_fraction")
        if modal_fraction is not None:
            _coerce_number(errors, source + ("sign_stability", "modal_fraction"), modal_fraction)
        for key in ("all_same",):
            value = sign_stability.get(key)
            if not isinstance(value, bool):
                _append_error(errors, source + ("sign_stability", key), "must be bool")
        for key in ("sign_changes", "longest_run"):
            value = sign_stability.get(key)
            if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                _append_error(errors, source + ("sign_stability", key), "must be a nonnegative integer")

        if isinstance(payload.get("frame_count"), int) and isinstance(payload.get("selected_frame_count"), int):
            if not isinstance(payload["frame_count"], bool) and not isinstance(payload["selected_frame_count"], bool):
                if payload["selected_frame_count"] != len(rows or []):
                    _append_error(errors, source + ("selected_frame_count",), "must match the number of rows")
            if isinstance(aggregate_counts, dict) and isinstance(aggregate_counts.get("selected_frame_count"), int):
                if aggregate_counts["selected_frame_count"] != payload["selected_frame_count"]:
                    _append_error(
                        errors,
                        source + ("aggregate_counts", "selected_frame_count"),
                        "must match top-level selected_frame_count",
                    )
            if isinstance(payload["frame_count"], int) and payload["frame_count"] < payload["selected_frame_count"]:
                _append_warning(
                    warnings,
                    source + ("frame_count",),
                    "frame_count is smaller than selected_frame_count; verify selection semantics",
                )

    for key in ("input", "output_json", "script", "requested_domain_length", "pressure_source", "source_proxy_source"):
        if key in payload and isinstance(payload[key], (int, float)) and not _is_finite_number(payload[key]):
            _append_error(errors, source + (key,), "must be finite numeric")

    if "domain_length" in payload:
        _coerce_number(errors, source + ("domain_length",), payload.get("domain_length"))

    if isinstance(rows, list):
        for row in rows:
            if isinstance(row, dict) and row.get("best_sign_proxy"):
                best = row["best_sign_proxy"]
                if isinstance(best, dict):
                    if row.get("best_sign") != best.get("sign"):
                        _append_error(errors, source + ("rows",), "best_sign must match best_sign_proxy.sign")
                    if isinstance(row.get("best_scale"), (int, float)) and isinstance(best.get("best_scale"), (int, float)):
                        if abs(float(row["best_scale"]) - float(best["best_scale"])) > 1.0e-12:
                            _append_error(errors, source + ("rows",), "best_scale must match best_sign_proxy.best_scale")

    return errors, warnings


def _validate_compare_selected_cell(cell: dict[str, Any], errors: list[str], path: tuple[Any, ...]) -> None:
    index = cell.get("index")
    if not isinstance(index, list) or len(index) != 3:
        _append_error(errors, path + ("index",), "must be a 3-item list")
    else:
        for idx, value in enumerate(index):
            if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                _append_error(errors, path + ("index", idx), f"must be a nonnegative integer, got {value!r}")

    tags = cell.get("tags")
    if not isinstance(tags, list):
        _append_error(errors, path + ("tags",), "must be a list")
    else:
        for idx, value in enumerate(tags):
            if not isinstance(value, str):
                _append_error(errors, path + ("tags", idx), f"must be a string, got {type(value).__name__}")

    raw = cell.get("raw")
    derived = cell.get("derived")
    delta = cell.get("delta")
    sign_mismatch = cell.get("sign_mismatch")

    if not isinstance(raw, dict):
        _append_error(errors, path + ("raw",), "must be an object")
    else:
        for key in COMPARE_CELL_RAW_KEYS:
            value = raw.get(key)
            _coerce_number(errors, path + ("raw", key), value)

    if not isinstance(derived, dict):
        _append_error(errors, path + ("derived",), "must be an object")
    else:
        for key in COMPARE_CELL_OPTIONAL_KEYS:
            value = derived.get(key)
            if value is not None:
                _coerce_number(errors, path + ("derived", key), value)

    if not isinstance(delta, dict):
        _append_error(errors, path + ("delta",), "must be an object")
    else:
        for key in COMPARE_CELL_OPTIONAL_KEYS:
            value = delta.get(key)
            if value is not None:
                _coerce_number(errors, path + ("delta", key), value)

    if not isinstance(sign_mismatch, dict):
        _append_error(errors, path + ("sign_mismatch",), "must be an object")
    else:
        for key in COMPARE_CELL_OPTIONAL_KEYS:
            value = sign_mismatch.get(key)
            if value is not None and not isinstance(value, bool):
                _append_error(errors, path + ("sign_mismatch", key), f"must be bool or null, got {type(value).__name__}")

    if isinstance(raw, dict) and isinstance(derived, dict) and isinstance(delta, dict) and isinstance(sign_mismatch, dict):
        for key in COMPARE_CELL_OPTIONAL_KEYS:
            raw_value = raw.get(key)
            derived_value = derived.get(key)
            delta_value = delta.get(key)
            mismatch_value = sign_mismatch.get(key)
            if raw_value is None or derived_value is None:
                continue
            if isinstance(raw_value, (int, float)) and isinstance(derived_value, (int, float)) and isinstance(delta_value, (int, float)):
                expected_delta = float(raw_value) - float(derived_value)
                if abs(expected_delta - float(delta_value)) > 1.0e-12:
                    _append_error(errors, path + ("delta", key), "must equal raw - derived")
                raw_sign = 0 if float(raw_value) == 0.0 else (1 if float(raw_value) > 0.0 else -1)
                derived_sign = 0 if float(derived_value) == 0.0 else (1 if float(derived_value) > 0.0 else -1)
                expected_mismatch = None
                if raw_sign != 0 and derived_sign != 0:
                    expected_mismatch = raw_sign != derived_sign
                if expected_mismatch is not None and mismatch_value is not None and mismatch_value != expected_mismatch:
                    _append_error(errors, path + ("sign_mismatch", key), "must match sign comparison")


def _validate_compare_payload(payload: dict[str, Any], path: Path) -> tuple[list[str], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []
    source = ("compare",)

    _check_contract(payload, COMPARE_CONTRACT, errors, source)
    _check_status(payload, errors, source)
    _check_control_card(payload, errors, source)
    _check_authority(payload, errors, source)
    _check_no_forbidden_promotion_flags(payload, errors, ())

    raw = payload.get("raw")
    derived = payload.get("derived")
    comparison = payload.get("comparison")
    summary = payload.get("summary")

    if not isinstance(raw, dict):
        _append_error(errors, source + ("raw",), "must be an object")
    else:
        for key in ("domain_length", "grid_spacing", "top_vorticity_value_sq", "top_vorticity_value"):
            if key in raw:
                value = raw.get(key)
                _coerce_number(errors, source + ("raw", key), value)
                if isinstance(value, (int, float)) and float(value) <= 0.0 and key in {"domain_length", "grid_spacing"}:
                    _append_error(errors, source + ("raw", key), "must be positive")

    if not isinstance(derived, dict):
        _append_error(errors, source + ("derived",), "must be an object")
    else:
        fields_present = derived.get("fields_present")
        if not isinstance(fields_present, list) or not fields_present:
            _append_error(errors, source + ("derived", "fields_present"), "must be a non-empty list")
        else:
            for idx, value in enumerate(fields_present):
                if not isinstance(value, str):
                    _append_error(errors, source + ("derived", "fields_present", idx), "must be a string")

    if not isinstance(comparison, dict):
        _append_error(errors, source + ("comparison",), "must be an object")
    else:
        requested_indices = comparison.get("requested_indices")
        comparison_indices = comparison.get("comparison_indices")
        selected_cells = comparison.get("selected_cells")

        for key, value in (("requested_indices", requested_indices), ("comparison_indices", comparison_indices)):
            if not isinstance(value, list):
                _append_error(errors, source + ("comparison", key), "must be a list")
            else:
                for idx, cell in enumerate(value):
                    if not isinstance(cell, list) or len(cell) != 3:
                        _append_error(errors, source + ("comparison", key, idx), "must be a 3-item list")
                    else:
                        for axis, coordinate in enumerate(cell):
                            if not isinstance(coordinate, int) or isinstance(coordinate, bool) or coordinate < 0:
                                _append_error(
                                    errors,
                                    source + ("comparison", key, idx, axis),
                                    f"must be a nonnegative integer, got {coordinate!r}",
                                )

        if not isinstance(selected_cells, list) or not selected_cells:
            _append_error(errors, source + ("comparison", "selected_cells"), "must be a non-empty list")
        else:
            for idx, cell in enumerate(selected_cells):
                if not isinstance(cell, dict):
                    _append_error(errors, source + ("comparison", "selected_cells", idx), "must be an object")
                    continue
                _validate_compare_selected_cell(cell, errors, source + ("comparison", "selected_cells", idx))

    if not isinstance(summary, dict):
        _append_error(errors, source + ("summary",), "must be an object")
    else:
        for key in (
            "raw_cell_count",
            "selected_cell_count",
            "requested_cell_count",
            "top_vorticity_cell_count",
        ):
            value = summary.get(key)
            if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                _append_error(errors, source + ("summary", key), f"must be a nonnegative integer, got {value!r}")

        field_stats = summary.get("field_stats")
        if not isinstance(field_stats, dict):
            _append_error(errors, source + ("summary", "field_stats"), "must be an object")
        else:
            for field in COMPARE_FIELD_KEYS:
                stats = field_stats.get(field)
                if not isinstance(stats, dict):
                    _append_error(errors, source + ("summary", "field_stats", field), "must be an object")
                    continue
                available = stats.get("available_count")
                mismatch = stats.get("sign_mismatch_count")
                if not isinstance(available, int) or isinstance(available, bool) or available < 0:
                    _append_error(
                        errors,
                        source + ("summary", "field_stats", field, "available_count"),
                        "must be a nonnegative integer",
                    )
                if not isinstance(mismatch, int) or isinstance(mismatch, bool) or mismatch < 0:
                    _append_error(
                        errors,
                        source + ("summary", "field_stats", field, "sign_mismatch_count"),
                        "must be a nonnegative integer",
                    )
                if isinstance(available, int) and isinstance(mismatch, int) and mismatch > available:
                    _append_error(
                        errors,
                        source + ("summary", "field_stats", field, "sign_mismatch_count"),
                        "cannot exceed available_count",
                    )
                for stat_key in ("mean_abs_delta", "max_abs_delta", "mean_raw", "mean_derived"):
                    value = stats.get(stat_key)
                    if value is not None:
                        _coerce_number(errors, source + ("summary", "field_stats", field, stat_key), value)
                if isinstance(stats.get("mean_abs_delta"), (int, float)) and isinstance(stats.get("max_abs_delta"), (int, float)):
                    if float(stats["max_abs_delta"]) < float(stats["mean_abs_delta"]):
                        _append_error(
                            errors,
                            source + ("summary", "field_stats", field, "max_abs_delta"),
                            "must be >= mean_abs_delta",
                        )
                if isinstance(stats.get("mean_raw"), (int, float)) and isinstance(stats.get("mean_derived"), (int, float)):
                    pass

        ordering = summary.get("raw_strain_eigenvalue_ordering")
        if not isinstance(ordering, dict):
            _append_error(errors, source + ("summary", "raw_strain_eigenvalue_ordering"), "must be an object")
        else:
            for key in ("lambda1_le_lambda2", "lambda2_le_lambda3"):
                value = ordering.get(key)
                if not isinstance(value, bool):
                    _append_error(errors, source + ("summary", "raw_strain_eigenvalue_ordering", key), "must be bool")

        derived_fields = summary.get("derived_fields_present")
        if not isinstance(derived_fields, list) or not derived_fields:
            _append_error(errors, source + ("summary", "derived_fields_present"), "must be a non-empty list")

    if isinstance(raw, dict) and isinstance(summary, dict):
        raw_cell_count = summary.get("raw_cell_count")
        if isinstance(raw_cell_count, int) and isinstance(raw.get("shape"), list):
            shape = raw["shape"]
            if len(shape) == 3 and all(isinstance(v, int) and not isinstance(v, bool) for v in shape):
                if shape[0] * shape[1] * shape[2] != raw_cell_count:
                    _append_error(errors, source + ("summary", "raw_cell_count"), "must match raw shape product")
        if isinstance(summary.get("selected_cell_count"), int) and isinstance(comparison.get("selected_cells"), list):
            if summary["selected_cell_count"] != len(comparison["selected_cells"]):
                _append_error(errors, source + ("summary", "selected_cell_count"), "must match selected_cells length")
        if isinstance(summary.get("requested_cell_count"), int) and isinstance(comparison.get("requested_indices"), list):
            if summary["requested_cell_count"] != len(comparison["requested_indices"]):
                _append_error(errors, source + ("summary", "requested_cell_count"), "must match requested_indices length")
        if isinstance(summary.get("top_vorticity_cell_count"), int) and summary["top_vorticity_cell_count"] != 1:
            _append_error(errors, source + ("summary", "top_vorticity_cell_count"), "must be 1")
    return errors, warnings


def _validate_budget_row(row: dict[str, Any], errors: list[str], path: tuple[Any, ...], has_pressure: bool) -> None:
    if row.get("status") != OK_STATUS:
        _append_error(errors, path + ("status",), f"must be {OK_STATUS!r}")
    frame = row.get("frame")
    if not isinstance(frame, int) or isinstance(frame, bool) or frame < 0:
        _append_error(errors, path + ("frame",), f"must be a nonnegative integer, got {frame!r}")

    selected_cell = row.get("selected_cell")
    if not isinstance(selected_cell, list) or len(selected_cell) != 3:
        _append_error(errors, path + ("selected_cell",), "must be a 3-item list")
    else:
        for idx, value in enumerate(selected_cell):
            if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                _append_error(errors, path + ("selected_cell", idx), f"must be a nonnegative integer, got {value!r}")

    for key in BUDGET_ROW_KEYS:
        value = row.get(key)
        _coerce_number(errors, path + (key,), value)
        if key in {"extensional_gain", "compressive_abs_gain", "omega_norm_sq", "omega_l3_domain_norm"}:
            if isinstance(value, (int, float)) and float(value) < 0.0:
                _append_error(errors, path + (key,), "must be nonnegative")

    pressure_laplacian = row.get("pressure_laplacian")
    if has_pressure:
        _coerce_number(errors, path + ("pressure_laplacian",), pressure_laplacian)
    else:
        if pressure_laplacian is not None:
            _coerce_number(errors, path + ("pressure_laplacian",), pressure_laplacian)


def _validate_budget_payload(payload: dict[str, Any], path: Path) -> tuple[list[str], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []
    source = ("budget",)

    _check_contract(payload, BUDGET_CONTRACT, errors, source)
    _check_status(payload, errors, source)
    _check_control_card(payload, errors, source)
    _check_authority(payload, errors, source)
    _check_no_forbidden_promotion_flags(payload, errors, ())

    for key in ("frame_count", "selected_frame_count"):
        value = payload.get(key)
        if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
            _append_error(errors, source + (key,), f"must be a positive integer, got {value!r}")

    selected_frames = payload.get("selected_frames")
    if not isinstance(selected_frames, list) or not selected_frames:
        _append_error(errors, source + ("selected_frames",), "must be a non-empty list")
    else:
        for idx, value in enumerate(selected_frames):
            if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                _append_error(errors, source + ("selected_frames", idx), f"must be a nonnegative integer, got {value!r}")
        if isinstance(payload.get("selected_frame_count"), int) and not isinstance(payload.get("selected_frame_count"), bool):
            if payload["selected_frame_count"] != len(selected_frames):
                _append_error(errors, source + ("selected_frame_count",), "must match selected_frames length")

    aggregate = payload.get("aggregate")
    aggregate_has_pressure = bool(aggregate.get("has_pressure_snapshots")) if isinstance(aggregate, dict) else False

    rows = payload.get("rows")
    if not isinstance(rows, list) or not rows:
        _append_error(errors, source + ("rows",), "must be a non-empty list")
    else:
        for idx, row in enumerate(rows):
            if not isinstance(row, dict):
                _append_error(errors, source + ("rows", idx), "must be an object")
                continue
            _validate_budget_row(row, errors, source + ("rows", idx), aggregate_has_pressure)

    if not isinstance(aggregate, dict):
        _append_error(errors, source + ("aggregate",), "must be an object")
    else:
        for key in ("frame_count", "selected_frame_count"):
            value = aggregate.get(key)
            if value is None and key in payload:
                value = payload.get(key)
            if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
                _append_error(errors, source + ("aggregate", key), f"must be a positive integer, got {value!r}")
        selected_frames_agg = aggregate.get("selected_frames")
        if not isinstance(selected_frames_agg, list) or not selected_frames_agg:
            _append_error(errors, source + ("aggregate", "selected_frames"), "must be a non-empty list")
        else:
            for idx, value in enumerate(selected_frames_agg):
                if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                    _append_error(
                        errors,
                        source + ("aggregate", "selected_frames", idx),
                        f"must be a nonnegative integer, got {value!r}",
                    )
            if isinstance(selected_frames, list) and selected_frames != selected_frames_agg:
                _append_error(errors, source + ("aggregate", "selected_frames"), "must match top-level selected_frames")

        has_pressure = aggregate.get("has_pressure_snapshots")
        if not isinstance(has_pressure, bool):
            _append_error(errors, source + ("aggregate", "has_pressure_snapshots"), "must be bool")
        for key in BUDGET_AGG_KEYS:
            stats = aggregate.get(key)
            if key == "pressure_laplacian" and not has_pressure:
                if stats is not None:
                    _append_error(errors, source + ("aggregate", key), "must be absent when pressure snapshots are unavailable")
                continue
            if key == "pressure_laplacian" and has_pressure is False:
                continue
            if key == "pressure_laplacian" and stats is None and has_pressure:
                _append_error(errors, source + ("aggregate", key), "must be present when pressure snapshots are available")
                continue
            if key != "pressure_laplacian" or has_pressure:
                if not isinstance(stats, dict):
                    _append_error(errors, source + ("aggregate", key), "must be an object")
                    continue
                _validate_stats(stats, errors, source + ("aggregate", key))
                if key in {"omega_norm_sq", "omega_l3_domain_norm"} and isinstance(stats.get("min"), (int, float)):
                    if float(stats["min"]) < 0.0:
                        _append_error(errors, source + ("aggregate", key, "min"), "must be nonnegative")

        if isinstance(rows, list) and isinstance(selected_frames_agg, list) and len(rows) != len(selected_frames_agg):
            _append_error(errors, source + ("aggregate", "selected_frames"), "must match rows length")
        if isinstance(payload.get("selected_frame_count"), int) and isinstance(rows, list):
            if payload["selected_frame_count"] != len(rows):
                _append_error(errors, source + ("selected_frame_count",), "must match rows length")

    return errors, warnings


def _build_output(
    status: str,
    errors: list[str],
    warnings: list[str],
    inputs: dict[str, str | None],
    changed_paths: list[str],
    checked_contracts: list[str],
) -> dict[str, Any]:
    return {
        "contract": CONTRACT,
        "status": status,
        "errors": sorted(set(errors)),
        "warnings": sorted(set(warnings)),
        "inputs": inputs,
        "changed_paths": changed_paths,
        "checked_contracts": checked_contracts,
        "script": SCRIPT_NAME,
        "O": "Regression checker for NS pressure-sign and interior budget convention diagnostics.",
        "R": "Validate sign timeseries, raw-derived comparisons, and budget timeseries JSON outputs.",
        "C": SCRIPT_NAME,
        "S": "Fail closed on schema, authority, sign-count, comparison, and budget aggregate violations.",
        "L": "Status is ok only when every requested input passes structural and numeric validation.",
        "P": "FAIL_CLOSED_NS_PRESSURE_CONVENTION_REGRESSION",
        "G": "No theorem, Clay, or promotion claim is introduced by this checker.",
        "F": "This checker only validates empirical diagnostics and their finite numeric summaries.",
    }


def main() -> int:
    pretty = False
    try:
        args = _parse_args()
        pretty = bool(args.pretty)
    except Exception as exc:
        result = _build_output(
            ERROR_STATUS,
            [str(exc)],
            [],
            {
                "sign_timeseries_json": None,
                "raw_derived_json": None,
                "budget_timeseries_json": None,
            },
            [],
            [],
        )
        print(json.dumps(result, sort_keys=True, indent=2 if pretty else None, ensure_ascii=False, allow_nan=False))
        return 1

    input_paths = {
        "sign_timeseries_json": args.sign_timeseries_json,
        "raw_derived_json": args.raw_derived_json,
        "budget_timeseries_json": args.budget_timeseries_json,
    }
    changed_paths = [str(path) for path in input_paths.values() if path is not None]
    checked_contracts: list[str] = []
    errors: list[str] = []
    warnings: list[str] = []

    if all(path is None for path in input_paths.values()):
        errors.append("provide at least one JSON input")

    if args.sign_timeseries_json is not None:
        checked_contracts.append(SIGN_CONTRACT)
        try:
            payload = _load_json(args.sign_timeseries_json)
            check_errors, check_warnings = _validate_sign_payload(payload, args.sign_timeseries_json)
            errors.extend(f"{args.sign_timeseries_json}: {message}" for message in check_errors)
            warnings.extend(f"{args.sign_timeseries_json}: {message}" for message in check_warnings)
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            errors.append(f"{args.sign_timeseries_json}: {exc}")

    if args.raw_derived_json is not None:
        checked_contracts.append(COMPARE_CONTRACT)
        try:
            payload = _load_json(args.raw_derived_json)
            check_errors, check_warnings = _validate_compare_payload(payload, args.raw_derived_json)
            errors.extend(f"{args.raw_derived_json}: {message}" for message in check_errors)
            warnings.extend(f"{args.raw_derived_json}: {message}" for message in check_warnings)
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            errors.append(f"{args.raw_derived_json}: {exc}")

    if args.budget_timeseries_json is not None:
        checked_contracts.append(BUDGET_CONTRACT)
        try:
            payload = _load_json(args.budget_timeseries_json)
            check_errors, check_warnings = _validate_budget_payload(payload, args.budget_timeseries_json)
            errors.extend(f"{args.budget_timeseries_json}: {message}" for message in check_errors)
            warnings.extend(f"{args.budget_timeseries_json}: {message}" for message in check_warnings)
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            errors.append(f"{args.budget_timeseries_json}: {exc}")

    status = OK_STATUS if not errors else ERROR_STATUS
    result = _build_output(
        status,
        errors,
        warnings,
        {name: None if path is None else str(path) for name, path in input_paths.items()},
        changed_paths,
        checked_contracts,
    )
    print(json.dumps(result, sort_keys=True, indent=2 if pretty else None, ensure_ascii=False, allow_nan=False))
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
