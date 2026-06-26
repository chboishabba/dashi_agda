#!/usr/bin/env python3
"""Regression checker for boundary pressure/geometry diagnostic JSON outputs."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_boundary_pressure_geometric_regression.py"
CONTRACT = "check_ns_boundary_pressure_geometric_regression"
OK_STATUS = "ok"
ERROR_STATUS = "error"

PRESSURE_CONTRACT = "ns_boundary_pressure_poisson_bypass_diagnostic"
GEOMETRIC_CONTRACT = "ns_boundary_geometric_concentration_diagnostic"

CHECK_TAG_KEYS = ("O", "R", "C", "S", "L", "P", "G", "F")

PRESSURE_EXPECTED_CELL_KEYS = ("analysis_cell_count",)

PRESSURE_OMEGA_COMPARISON_KEYS = ("omega_comparison", "omegaComparison")
PRESSURE_VIOLATION_COUNT_KEYS = ("violation_count",)
PRESSURE_MAX_VIOLATION_KEYS = ("max_violation",)

GEOMETRIC_TOP_CELL_KEYS = (
    "top_cell_count",
    "top_k_cell_count",
    "selected_top_cell_count",
)
GEOMETRIC_ANALYSIS_CELL_KEYS = (
    "analysis_cell_count",
    "analysis_mask_cell_count",
    "analysis_cells",
)
GEOMETRIC_WORST_ID_KEYS = (
    "worst_cell_id",
    "worst_cell_index",
    "worst_cell",
)
GEOMETRIC_WORST_VALUE_KEYS = (
    "worst_cell_fraction",
    "worst_fraction",
    "worst_cell_value",
    "worst_cell_ratio",
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--pressure-json",
        type=Path,
        default=None,
        help="Pressure Poisson bypass diagnostic JSON path.",
    )
    parser.add_argument(
        "--geometric-json",
        type=Path,
        default=None,
        help="Geometric concentration diagnostic JSON path.",
    )
    parser.add_argument(
        "--pretty",
        action="store_true",
        help="Pretty-print JSON output.",
    )
    return parser.parse_args()


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing input file: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"top-level JSON payload is not an object: {path}")
    return payload


def _record_error(errors: list[str], path_label: str, message: str) -> None:
    errors.append(f"{path_label}: {message}")


def _record_warning(warnings: list[str], path_label: str, message: str) -> None:
    warnings.append(f"{path_label}: {message}")


def _normalize_key(value: str) -> str:
    return "".join(character.lower() for character in value if character.isalnum())


def _get_by_alias(payload: dict[str, Any], aliases: tuple[str, ...]) -> tuple[str | None, Any]:
    for key in aliases:
        if key in payload:
            return key, payload[key]
    normalized_aliases = {_normalize_key(alias): alias for alias in aliases}
    for key, value in payload.items():
        if _normalize_key(str(key)) in normalized_aliases:
            return key, value
    return None, None


def _require_nonnegative_int(
    payload: dict[str, Any],
    path_label: str,
    key_aliases: tuple[str, ...],
    errors: list[str],
) -> int | None:
    key, value = _get_by_alias(payload, key_aliases)
    if key is None:
        _record_error(errors, path_label, f"missing required field {key_aliases[0]!r}")
        return None

    if isinstance(value, bool) or not isinstance(value, int):
        _record_error(errors, path_label, f"{key} must be a nonnegative integer, got {value!r}")
        return None
    if value < 0:
        _record_error(errors, path_label, f"{key} must be nonnegative, got {value}")
        return None
    return value


def _coerce_finite_numeric(
    payload: dict[str, Any],
    path_label: str,
    key_aliases: tuple[str, ...],
    errors: list[str],
    *,
    allow_bool: bool = False,
) -> float | None:
    key, value = _get_by_alias(payload, key_aliases)
    if key is None:
        if len(key_aliases) == 1:
            _record_error(errors, path_label, f"missing required field {key_aliases[0]!r}")
        else:
            _record_error(
                errors,
                path_label,
                f"missing required field (aliases: {', '.join(key_aliases)})",
            )
        return None

    if isinstance(value, bool):
        if allow_bool:
            return None
        _record_error(errors, path_label, f"{key} must be numeric, got bool")
        return None
    if not isinstance(value, (int, float)):
        _record_error(errors, path_label, f"{key} must be numeric, got {type(value).__name__}")
        return None
    value_f = float(value)
    if not math.isfinite(value_f):
        _record_error(errors, path_label, f"{key} must be finite, got {value!r}")
        return None
    return value_f


def _require_contract(payload: dict[str, Any], path_label: str, expected: str, errors: list[str]) -> None:
    contract = payload.get("contract")
    if not isinstance(contract, str):
        _record_error(errors, path_label, "contract must be a non-empty string")
        return
    if contract != expected:
        _record_error(errors, path_label, f"contract mismatch: {contract!r} (expected {expected!r})")


def _require_tags(payload: dict[str, Any], path_label: str, errors: list[str]) -> None:
    for key in CHECK_TAG_KEYS:
        value = payload.get(key)
        if not isinstance(value, str) or not value.strip():
            _record_error(errors, path_label, f"{key} must be a non-empty string")


def _require_authority_false(payload: dict[str, Any], path_label: str, errors: list[str]) -> bool:
    authority = payload.get("authority")
    if not isinstance(authority, dict):
        _record_error(errors, path_label, "authority must be a non-empty object")
        return False
    if not authority:
        _record_error(errors, path_label, "authority object must not be empty")
        return False

    keys_to_check: tuple[tuple[str, tuple[str, ...]], ...] = (
        ("promoted", ("promoted", "promotion")),
        ("clay_authority", ("clay_authority", "clay_promotion")),
        ("theorem_authority", ("theorem_authority", "theorem_promotion")),
    )

    passed = True
    for _, aliases in keys_to_check:
        found_key, found_value = _get_by_alias(authority, aliases)
        if found_key is None:
            _record_error(errors, f"{path_label}::authority", f"missing required key {aliases[0]!r}")
            passed = False
            continue
        if not isinstance(found_value, bool):
            _record_error(
                errors,
                f"{path_label}::authority::{found_key}",
                f"must be bool, got {type(found_value).__name__}",
            )
            passed = False
            continue
        if found_value:
            _record_error(
                errors,
                f"{path_label}::authority::{found_key}",
                "must be false for this diagnostic checker",
            )
            passed = False
    return passed


def _check_promotion_flags(payload: dict[str, Any], path_label: str, errors: list[str]) -> None:
    for key, value in payload.items():
        if key == "authority" or not isinstance(value, bool):
            continue
        normalized = _normalize_key(str(key))
        if ("promotion" in normalized or "promoting" in normalized or "promoted" in normalized):
            if value:
                _record_error(errors, path_label, f"{key} must be false")


def _validate_pressure(payload: dict[str, Any], path_label: str, errors: list[str]) -> bool:
    _require_contract(payload, path_label, PRESSURE_CONTRACT, errors)
    _require_tags(payload, path_label, errors)
    authority_ok = _require_authority_false(payload, path_label, errors)
    _check_promotion_flags(payload, path_label, errors)

    _require_nonnegative_int(payload, path_label, PRESSURE_EXPECTED_CELL_KEYS, errors)

    comparison_key, omega_payload = _get_by_alias(payload, PRESSURE_OMEGA_COMPARISON_KEYS)
    if comparison_key is not None:
        if not isinstance(omega_payload, dict):
            _record_error(errors, f"{path_label}::{comparison_key}", "must be an object")
        else:
            _require_nonnegative_int(
                omega_payload,
                f"{path_label}::{comparison_key}",
                PRESSURE_VIOLATION_COUNT_KEYS,
                errors,
            )
            _coerce_finite_numeric(
                omega_payload,
                f"{path_label}::{comparison_key}",
                PRESSURE_MAX_VIOLATION_KEYS,
                errors,
            )
    return authority_ok


def _validate_geometric(payload: dict[str, Any], path_label: str, errors: list[str]) -> bool:
    _require_contract(payload, path_label, GEOMETRIC_CONTRACT, errors)
    _require_tags(payload, path_label, errors)
    authority_ok = _require_authority_false(payload, path_label, errors)
    _check_promotion_flags(payload, path_label, errors)

    analysis_count = _require_nonnegative_int(payload, path_label, GEOMETRIC_ANALYSIS_CELL_KEYS, errors)
    top_count = _require_nonnegative_int(payload, path_label, GEOMETRIC_TOP_CELL_KEYS, errors)
    if analysis_count is not None and top_count is not None:
        if top_count > analysis_count:
            _record_error(
                errors,
                path_label,
                "top_cell_count must not exceed analysis_cell_count",
            )

    for key, value in payload.items():
        if not isinstance(key, str):
            continue
        if "fraction" not in _normalize_key(key):
            continue
        if key in (
            "fraction_field_count",
            "cell_fraction_count",
            "input_fraction",
        ):
            # Skip fields with unrelated fraction-like names that are not diagnostics.
            continue
        if isinstance(value, bool):
            continue
        if isinstance(value, (int, float)):
            value_f = float(value)
            if not math.isfinite(value_f) or not (0.0 <= value_f <= 1.0):
                _record_error(
                    errors,
                    f"{path_label}::{key}",
                    f"fraction-like field must be finite in [0, 1], got {value!r}",
                )
        elif isinstance(value, dict) and "fraction" in _normalize_key(key):
            _record_error(
                errors,
                f"{path_label}::{key}",
                "fraction-like field must be numeric",
            )

    worst_id_key, _ = _get_by_alias(payload, GEOMETRIC_WORST_ID_KEYS)
    worst_value_key, _ = _get_by_alias(payload, GEOMETRIC_WORST_VALUE_KEYS)
    if worst_id_key is None:
        _record_error(
            errors,
            path_label,
            "missing required worst-cell identity field (aliases: "
            + ", ".join(GEOMETRIC_WORST_ID_KEYS)
            + ")",
        )
    if worst_value_key is None:
        _record_error(
            errors,
            path_label,
            "missing required worst-cell value field (aliases: "
            + ", ".join(GEOMETRIC_WORST_VALUE_KEYS)
            + ")",
        )

    return authority_ok


def main() -> int:
    args = _parse_args()
    if args.pressure_json is None and args.geometric_json is None:
        result = {
            "contract": CONTRACT,
            "status": ERROR_STATUS,
            "errors": ["at least one of --pressure-json or --geometric-json is required"],
            "warnings": [],
            "checked_contracts": [],
            "authority_false": False,
            "inputs": {"pressure_json": None, "geometric_json": None},
            "changed_files": [],
            "O": "Regression checker for pressure-poisson and geometric concentration diagnostic JSON.",
            "R": "validate contracts, authority constraints, and numeric guardrails for regression artifacts",
            "C": SCRIPT_NAME,
            "S": "Fail-closed on required field/type mismatches and forbidden promotion flags.",
            "L": "Non-empty metadata and consistency checks are hard errors; optional diagnostics are warnings only.",
            "P": "FAIL_CLOSED_NS_BOUNDARY_PRESSURE_GEOMETRIC_REGRESSION",
            "G": "No theorem, Clay, or promotion claim is inferred by this checker.",
            "F": "This regression script only validates generated diagnostic output.",
        }
        print(json.dumps(result, sort_keys=True, indent=2 if args.pretty else None))
        return 1

    errors: list[str] = []
    warnings: list[str] = []
    checked_contracts: list[str] = []
    changed_files: list[str] = []
    all_authority_false = True
    inputs = {"pressure_json": None, "geometric_json": None}

    if args.pressure_json is not None:
        path = args.pressure_json
        inputs["pressure_json"] = str(path)
        changed_files.append(str(path))
        checked_contracts.append(PRESSURE_CONTRACT)
        try:
            payload = _load_json(path)
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            errors.append(f"{path}: {exc}")
            all_authority_false = False
        else:
            all_authority_false &= _validate_pressure(payload, str(path), errors)

    if args.geometric_json is not None:
        path = args.geometric_json
        inputs["geometric_json"] = str(path)
        changed_files.append(str(path))
        checked_contracts.append(GEOMETRIC_CONTRACT)
        try:
            payload = _load_json(path)
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            errors.append(f"{path}: {exc}")
            all_authority_false = False
        else:
            all_authority_false &= _validate_geometric(payload, str(path), errors)

    status = ERROR_STATUS if errors else OK_STATUS
    result: dict[str, Any] = {
        "contract": CONTRACT,
        "status": status,
        "errors": sorted(set(errors)),
        "warnings": sorted(set(warnings)),
        "checked_contracts": sorted(set(checked_contracts)),
        "authority_false": (all_authority_false and not errors),
        "inputs": inputs,
        "changed_files": sorted(set(changed_files)),
        "O": "Regression checker for pressure-poisson and geometric concentration diagnostic JSON.",
        "R": "validate contracts, authority constraints, and numeric guardrails for regression artifacts",
        "C": SCRIPT_NAME,
        "S": "Fail-closed on required field/type mismatches and forbidden promotion flags.",
        "L": "Non-empty metadata and consistency checks are hard errors; optional diagnostics are warnings only.",
        "P": "FAIL_CLOSED_NS_BOUNDARY_PRESSURE_GEOMETRIC_REGRESSION",
        "G": "No theorem, Clay, or promotion claim is inferred by this checker.",
        "F": "This regression script only validates generated diagnostic output.",
    }

    print(json.dumps(result, sort_keys=True, indent=2 if args.pretty else None))
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
