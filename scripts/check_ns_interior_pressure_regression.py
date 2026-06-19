#!/usr/bin/env python3
"""Regression checker for interior budget and omega L3 timeseries diagnostics."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_interior_pressure_regression.py"
CONTRACT = "check_ns_interior_pressure_regression"
L3_CONTRACT = "ns_omega_l3_timeseries_diagnostic"
OK_STATUS = "ok"
ERROR_STATUS = "error"


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--interior-json",
        type=Path,
        default=None,
        help="Path to the interior pressure budget diagnostic JSON.",
    )
    parser.add_argument(
        "--l3-json",
        type=Path,
        default=None,
        help="Path to the omega L3 timeseries diagnostic JSON.",
    )
    parser.add_argument(
        "--pretty",
        action="store_true",
        help="Pretty-print deterministic JSON output.",
    )
    return parser.parse_args()


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing input file: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"top-level payload must be an object: {path}")
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
    prefix = _join_path(path)
    errors.append(f"{prefix}: {message}" if prefix else message)


def _append_warning(warnings: list[str], path: tuple[Any, ...], message: str) -> None:
    prefix = _join_path(path)
    warnings.append(f"{prefix}: {message}" if prefix else message)


def _is_finite_number(value: Any) -> bool:
    if isinstance(value, bool):
        return False
    if isinstance(value, int):
        return True
    if isinstance(value, float):
        return math.isfinite(value)
    return False


def _is_nonnegative_integer(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


def _check_control_card(payload: dict[str, Any], source: str, errors: list[str]) -> None:
    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        value = payload.get(key)
        if not isinstance(value, str) or not value.strip():
            errors.append(f"{source}: missing required control-card field {key!r} or value is empty")


def _check_authority_false(payload: dict[str, Any], source: str, errors: list[str]) -> None:
    authority = payload.get("authority")
    if authority is None:
        errors.append(f"{source}: missing authority object")
        return
    if not isinstance(authority, dict):
        errors.append(f"{source}: authority must be an object, got {type(authority).__name__}")
        return

    allowed_true = {"candidate_only", "empirical_non_promoting", "diagnostic_only"}
    for key, value in sorted(authority.items(), key=lambda item: str(item[0])):
        if isinstance(value, bool):
            if value and str(key) not in allowed_true:
                errors.append(f"{source}: authority[{key!r}] must be false")
        elif value is None:
            continue
        elif isinstance(value, (int, float, str, list, tuple, dict)):
            if isinstance(value, (int, float)) and not _is_finite_number(value):
                errors.append(f"{source}: authority[{key!r}] must be finite, got {value!r}")
            elif not isinstance(value, bool):
                errors.append(
                    f"{source}: authority[{key!r}] must be boolean, got {type(value).__name__}"
                )


def _is_promotion_flag_key(key: str) -> bool:
    normalized = _normalize_key(key)
    if normalized in {"empiricalnonpromoting", "nonpromoting", "candidateonly", "diagnosticonly"}:
        return False
    return (
        "promotion" in normalized
        or "promoting" in normalized
        or "promoted" in normalized
        or "theorem" in normalized
        or "clay" in normalized
    )


def _check_promotion_flags(
    node: Any,
    path: tuple[Any, ...],
    source: str,
    errors: list[str],
) -> None:
    if isinstance(node, dict):
        for key, value in node.items():
            if isinstance(key, str) and _is_promotion_flag_key(key) and isinstance(value, bool):
                if value:
                    errors.append(
                        f"{_join_path(path)}: boolean flag {key!r} must be false in {source}"
                    )
            _check_promotion_flags(value, path + (key,), source, errors)
        return
    if isinstance(node, list):
        for index, value in enumerate(node):
            _check_promotion_flags(value, path + (index,), source, errors)


def _walk_finite_fields(node: Any, path: tuple[Any, ...], source: str, errors: list[str]) -> None:
    if node is None:
        return
    if isinstance(node, bool):
        return
    if isinstance(node, (int, float)):
        if isinstance(node, float) and not math.isfinite(node):
            _append_error(errors, path, f"{source}: non-finite numeric value {node!r}")
        return
    if isinstance(node, (list, tuple)):
        for index, item in enumerate(node):
            _walk_finite_fields(item, path + (index,), source, errors)
        return
    if isinstance(node, dict):
        for key, value in node.items():
            _walk_finite_fields(value, path + (key,), source, errors)


def _collect_numeric_keys(node: Any, path: tuple[Any, ...], predicate, results: list[tuple[tuple[Any, ...], Any]]) -> None:
    if node is None:
        return
    if isinstance(node, dict):
        for key, value in node.items():
            if not isinstance(key, str):
                _collect_numeric_keys(value, path + (key,), predicate, results)
                continue
            if predicate(key):
                results.append((path + (key,), value))
            _collect_numeric_keys(value, path + (key,), predicate, results)
        return
    if isinstance(node, (list, tuple)):
        for index, item in enumerate(node):
            _collect_numeric_keys(item, path + (index,), predicate, results)


def _ensure_finite_named_value(
    source: str,
    key: str,
    value: Any,
    path: tuple[Any, ...],
    warnings: list[str],
    errors: list[str],
    integer_only: bool = False,
) -> None:
    if isinstance(value, bool) or value is None:
        warnings.append(f"{source}: {key}: unexpected null/bool value")
        return
    if integer_only:
        if not _is_nonnegative_integer(value):
            errors.append(f"{source}: {key}: must be a nonnegative integer, got {value!r}")
        return

    if isinstance(value, (int, float)):
        if isinstance(value, float) and not math.isfinite(value):
            errors.append(f"{source}: {key}: must be finite numeric, got {value!r}")
        return
    if isinstance(value, (list, tuple)):
        for index, item in enumerate(value):
            _ensure_finite_named_value(
                source,
                key,
                item,
                path + (index,),
                warnings,
                errors,
                integer_only=False,
            )
        return
    if isinstance(value, dict):
        for sub_key, sub_value in value.items():
            _ensure_finite_named_value(
                source,
                f"{key}.{sub_key}",
                sub_value,
                path + (sub_key,),
                warnings,
                errors,
                integer_only=False,
            )
        return
    warnings.append(f"{source}: {key}: expected numeric-like value, got {type(value).__name__}")


def _check_selected_cell_fields(
    payload: dict[str, Any], source: str, warnings: list[str], errors: list[str]
) -> None:
    for key, value in payload.items():
        if not isinstance(key, str):
            continue
        key_norm = _normalize_key(key)
        if "selected" not in key_norm or "cell" not in key_norm:
            continue
        if "count" in key_norm or "selectedcount" in key_norm:
            _ensure_finite_named_value(
                source,
                key,
                value,
                ("interior",),
                warnings,
                errors,
                integer_only=True,
            )
        else:
            _ensure_finite_named_value(
                source,
                key,
                value,
                ("interior",),
                warnings,
                errors,
                integer_only=False,
            )
            if isinstance(value, (list, tuple)):
                for item in value:
                    if isinstance(item, (list, tuple)):
                        for coordinate in item:
                            if not _is_nonnegative_integer(coordinate):
                                errors.append(
                                    f"{source}: {key}: selected cell coordinates must be nonnegative integers, got {coordinate!r}"
                                )
                                break


def _check_lambda_eigen_fields(
    payload: dict[str, Any], source: str, warnings: list[str], errors: list[str]
) -> None:
    matches: list[tuple[tuple[Any, ...], Any]] = []
    predicate = lambda key: ("lambda" in _normalize_key(key)) or ("eigen" in _normalize_key(key))
    _collect_numeric_keys(payload, (), predicate, matches)
    for path, value in matches:
        key = _join_path(path)
        _ensure_finite_named_value(source, key, value, path, warnings, errors, integer_only=False)


def _check_budget_fields(
    payload: dict[str, Any], source: str, warnings: list[str], errors: list[str]
) -> None:
    matches: list[tuple[tuple[Any, ...], Any]] = []
    predicate = lambda key: (
        "budget" in _normalize_key(key)
        or _normalize_key(key).endswith("loss")
        or _normalize_key(key).endswith("gain")
    )
    _collect_numeric_keys(payload, (), predicate, matches)
    for path, value in matches:
        key = _join_path(path)
        _ensure_finite_named_value(source, key, value, path, warnings, errors, integer_only=False)


def _check_frame_fields(
    payload: dict[str, Any], source: str, errors: list[str], warnings: list[str]
) -> None:
    frame_count = payload.get("frame_count")
    if frame_count is not None:
        if not _is_nonnegative_integer(frame_count):
            errors.append(f"{source}: frame_count must be a nonnegative integer, got {frame_count!r}")

    rows = payload.get("rows")
    if rows is not None:
        if not isinstance(rows, list):
            errors.append(f"{source}: rows must be a list, got {type(rows).__name__}")
        else:
            frame_values: list[int] = []
            for index, row in enumerate(rows):
                if not isinstance(row, dict):
                    errors.append(f"{source}: rows[{index}] must be an object")
                    continue
                if "frame" in row:
                    frame = row.get("frame")
                    if not _is_nonnegative_integer(frame):
                        errors.append(f"{source}: rows[{index}].frame must be a nonnegative integer")
                    else:
                        frame_values.append(frame)
                        if isinstance(frame_count, int) and frame >= frame_count:
                            warnings.append(
                                f"{source}: rows[{index}].frame={frame} is outside frame_count={frame_count}"
                            )
            if frame_count is not None and frame_count != len(rows):
                warnings.append(
                    f"{source}: rows length {len(rows)} does not match frame_count {frame_count}"
                )
            if frame_values and sorted(frame_values) != list(range(min(frame_values), min(frame_values) + len(frame_values))):
                warnings.append(f"{source}: frame indices are not contiguous")

    for timing_key in ("time", "steps"):
        series = payload.get(timing_key)
        if series is None:
            continue
        if not isinstance(series, list):
            errors.append(f"{source}: {timing_key} must be a list")
            continue
        if not all(isinstance(item, (int, float)) for item in series):
            errors.append(f"{source}: {timing_key} must contain numeric entries")
        if frame_count is not None and len(series) not in (0, frame_count):
            warnings.append(f"{source}: {timing_key} length {len(series)} mismatches frame_count {frame_count}")


def _check_status(payload: dict[str, Any], source: str, warnings: list[str]) -> None:
    status = payload.get("status")
    if status is None:
        warnings.append(f"{source}: missing status")
        return
    if not isinstance(status, str):
        warnings.append(f"{source}: status should be a string, got {type(status).__name__}")
        return
    if status != OK_STATUS and status != "error":
        warnings.append(f"{source}: status is {status!r}, expected {OK_STATUS!r} or {ERROR_STATUS!r}")


def _check_l3_fields(payload: dict[str, Any], source: str, errors: list[str], warnings: list[str]) -> None:
    contract = payload.get("contract")
    if contract is not None and contract != L3_CONTRACT:
        warnings.append(f"{source}: contract mismatch: got {contract!r}, expected {L3_CONTRACT!r}")

    _check_frame_fields(payload, source, errors, warnings)
    _check_status(payload, source, warnings)

    integration_method = payload.get("integration_method")
    if integration_method is not None and integration_method not in {"trapz", "sum"}:
        warnings.append(
            f"{source}: integration_method={integration_method!r}; expected 'trapz' or 'sum'"
        )

    rows = payload.get("rows", [])
    if not isinstance(rows, list):
        return
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            continue
        row_path = f"rows[{index}]"
        status = row.get("status")
        if status is not None and not isinstance(status, str):
            warnings.append(f"{source}: {row_path}.status should be string, got {type(status).__name__}")
        for key in ("omega_l3_norm", "omega_linf", "omega_l2_norm", "mean", "max_value"):
            if key in row:
                if not isinstance(row[key], (int, float)) or isinstance(row[key], bool):
                    errors.append(f"{source}: {row_path}.{key} must be numeric")
                elif isinstance(row[key], float) and not math.isfinite(row[key]):
                    errors.append(f"{source}: {row_path}.{key} must be finite, got {row[key]!r}")
        for key in ("omega_l2_sq_domain_integral", "omega_l3_domain_integral"):
            if key in row:
                if not isinstance(row[key], (int, float)) or isinstance(row[key], bool):
                    errors.append(f"{source}: {row_path}.{key} must be numeric")
                elif isinstance(row[key], float) and not math.isfinite(row[key]):
                    errors.append(f"{source}: {row_path}.{key} must be finite, got {row[key]!r}")
        for key in ("finite_cell_count", "total_cell_count"):
            if key in row and not _is_nonnegative_integer(row[key]):
                errors.append(
                    f"{source}: {row_path}.{key} must be a nonnegative integer, got {row[key]!r}"
                )
        max_index = row.get("max_index")
        if max_index is not None:
            if not isinstance(max_index, (list, tuple)):
                errors.append(f"{source}: {row_path}.max_index must be a list/tuple")
            elif len(max_index) != 3:
                errors.append(f"{source}: {row_path}.max_index must have length 3, got {len(max_index)}")
            elif not all(_is_nonnegative_integer(item) for item in max_index):
                errors.append(f"{source}: {row_path}.max_index entries must be nonnegative integers")


def _check_interior_payload(
    payload: dict[str, Any], source: str, errors: list[str], warnings: list[str]
) -> None:
    _check_control_card(payload, source, errors)
    _check_authority_false(payload, source, errors)
    _check_promotion_flags(payload, (source,), source, errors)
    _check_status(payload, source, warnings)
    _check_frame_fields(payload, source, errors, warnings)
    _check_selected_cell_fields(payload, source, warnings, errors)
    _check_lambda_eigen_fields(payload, source, warnings, errors)
    _check_budget_fields(payload, source, warnings, errors)

    # Best-effort finite numeric hygiene: reject NaN/inf and bad numeric leaves in nested
    # structures while still treating non-numeric payload as informational.
    _walk_finite_fields(payload, (source,), source, errors)


def _build_result(
    interior_path: Path | None,
    l3_path: Path | None,
    errors: list[str],
    warnings: list[str],
) -> dict[str, Any]:
    status = ERROR_STATUS if errors else OK_STATUS
    changed_files = [str(path) for path in (interior_path, l3_path) if path is not None]
    return {
        "contract": CONTRACT,
        "status": status,
        "errors": sorted(set(errors)),
        "warnings": sorted(set(warnings)),
        "inputs": {
            "interior_json": None if interior_path is None else str(interior_path),
            "l3_json": None if l3_path is None else str(l3_path),
        },
        "changed_files": sorted(set(changed_files)),
        "changed_paths": sorted(set(changed_files)),
        "O": "Regression checker for interior pressure budget and omega L3 timeseries diagnostics.",
        "R": (
            "Fail-closed validation of interior budget fields, frame counts, selected cells, "
            "lambda/eigenbasis fields, budgets, and L3-row numeric integrity."
        ),
        "C": SCRIPT_NAME,
        "S": (
            "Checks are best-effort across diagnostic outputs and require non-promotion authority "
            "with finite numerics on declared output contracts."
        ),
        "L": (
            "Errors indicate schema or numeric violations; promotion/authority violations remain hard failures."
        ),
        "P": "FAIL_CLOSED_NS_INTERIOR_PRESSURE_REGRESSION",
        "G": "No theorem, Clay, or theorem-promotion claim is introduced by this checker.",
        "F": (
            "No pressure route closure is inferred; this checker validates deterministic finite-"
            "numeric diagnostic outputs only."
        ),
    }


def main() -> int:
    args = _parse_args()
    errors: list[str] = []
    warnings: list[str] = []

    interior_path = args.interior_json
    l3_path = args.l3_json

    if interior_path is None and l3_path is None:
        result = _build_result(
            interior_path,
            l3_path,
            ["no input path provided: use --interior-json, --l3-json, or both"],
            [],
        )
        print(
            json.dumps(
                result,
                sort_keys=True,
                indent=2 if args.pretty else None,
                ensure_ascii=False,
            )
        )
        return 1

    if interior_path is not None:
        try:
            payload = _load_json(interior_path)
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            errors.append(f"{interior_path}: {exc}")
        else:
            _check_interior_payload(payload, "interior", errors, warnings)

    if l3_path is not None:
        try:
            payload = _load_json(l3_path)
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            errors.append(f"{l3_path}: {exc}")
        else:
            _check_l3_fields(payload, "l3", errors, warnings)
            _check_control_card(payload, "l3", errors)
            # Keep a best-effort consistency check between the two diagnostics when both exist.
            if payload.get("contract") == L3_CONTRACT:
                _check_authority_false(payload, "l3", errors)
                _check_status(payload, "l3", warnings)

    result = _build_result(interior_path, l3_path, errors, warnings)
    print(
        json.dumps(
            result,
            sort_keys=True,
            indent=2 if args.pretty else None,
            ensure_ascii=False,
        )
    )
    return 0 if result["status"] == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
