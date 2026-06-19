#!/usr/bin/env python3
"""Regression checker for NS boundary empirical outputs."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


CONTRACT = "check_ns_boundary_empirical_regression"
EXPECTED_COMPONENT_CONTRACT = "ns_boundary_component_lambda3_diagnostic"
EXPECTED_F123_CONTRACT = "ns_boundary_f123_absorption_diagnostic"
OK_STATUS = "ok"
FAIL_CLOSED = "fail_closed"


REQUIRED_AUTHORITIES = {
    "candidate_only": True,
    "empirical_non_promoting": True,
    "truth_authority": False,
    "theorem_authority": False,
    "clay_authority": False,
    "runtime_authority": False,
    "promoted": False,
}


REQUIRED_COMPONENT_NUMERIC = (
    "component_count",
    "component_id",
    "component_cell_count",
    "boundary_cell_count",
    "tight_band_cell_count",
    "component_diameter_cells",
    "lambda3_min_abs",
    "min_g12_value",
    "min_rho_value",
)


REQUIRED_F123_NUMERIC = (
    "boundary_cell_count",
    "analysis_mask_cell_count",
    "selected_density_cells",
    "damping_sum_abs",
    "damping_sum_signed",
    "g12_nonpositive_in_analysis",
    "g12_zero_or_nonpositive_cells",
)


REQUIRED_SUMMARY_FLAGS = (
    ("lambda3_distribution_empirical", ("lambda3_distribution_empirical", "lambda3DistributionEmpirical"), True),
    ("lambda3_distribution_promoting", ("lambda3_distribution_promoting", "lambda3DistributionPromoting"), False),
    ("h_delta1_hypothesis", ("h_delta1_hypothesis", "hDelta1Hypothesis"), True),
    ("h_delta1_promoting", ("h_delta1_promoting", "hDelta1Promoting", "h_delta1_is_promoting", "hDelta1IsPromoting"), False),
    ("f123_absorption_support_only", ("f123_absorption_support_only", "f123AbsorptionSupportOnly"), True),
    ("commutator_comparison_measured", ("commutator_comparison_measured", "commutatorComparisonMeasured"), False),
    ("commutator_comparison_proxy_unavailable", ("commutator_comparison_proxy_unavailable", "commutatorComparisonProxyUnavailable"), True),
    ("korn_level_set", ("korn_level_set", "kornLevelSet"), False),
    ("collapse_impossible", ("collapse_impossible", "collapseImpossible"), False),
    ("clay_promotion", ("clay_promotion", "clayPromotion"), False),
)


REQUIRED_COMPONENT_KEYS_OK = {
    "shape": (list,),
    "analysis_mask_source": (str,),
    "authority": (dict,),
    "status": (str,),
    "contract": (str,),
    "component_count": (int,),
    "component_id": (int,),
    "component_cell_count": (int,),
    "boundary_cell_count": (int,),
    "tight_band_cell_count": (int,),
    "component_diameter_cells": (float, int),
    "lambda3_min_abs": (float, int),
    "lambda3_bounded_away_from_zero": (bool,),
    "min_g12": (dict,),
    "min_g12_value": (float, int),
    "min_rho": (dict,),
    "min_rho_value": (float, int),
    "lambda3_stats": (dict,),
    "boundary_lambda3_stats": (dict,),
    "tight_band_lambda3_stats": (dict,),
}


REQUIRED_F123_KEYS_OK = {
    "shape": (list,),
    "authority": (dict,),
    "status": (str,),
    "contract": (str,),
    "input_shape": (list,),
    "selected_density_cells": (int,),
    "damping_sum_abs": (float, int),
    "damping_sum_signed": (float, int),
    "density_stats": (dict,),
    "abs_damping_stats": (dict,),
    "boundary_cell_count": (int,),
    "analysis_mask_cell_count": (int,),
    "dominance": (dict,),
}


def _normalize_key(value: str) -> str:
    return "".join(character.lower() for character in value if character.isalnum())


def _path_to_string(path: tuple[Any, ...]) -> str:
    parts: list[str] = []
    for entry in path:
        if isinstance(entry, int):
            parts.append(f"[{entry}]")
        else:
            parts.append(str(entry))
    return "".join(parts).lstrip(".")


def _record_error(errors: list[str], path: tuple[Any, ...], message: str) -> None:
    if not path:
        errors.append(message)
    else:
        errors.append(f"{_path_to_string(path)}: {message}")


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing input file: {path}")
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"top-level JSON payload for {path} is not an object")
    return data


def _find_field(payload: dict[str, Any], aliases: tuple[str, ...]) -> tuple[str | None, Any | None]:
    for alias in aliases:
        if alias in payload:
            return alias, payload[alias]
    normalized = {_normalize_key(alias): alias for alias in aliases}
    for key, value in payload.items():
        if _normalize_key(key) in normalized:
            return key, value
    return None, None


def _require_status(payload: dict[str, Any], scope: str, errors: list[str]) -> None:
    status = payload.get("status")
    if status is None:
        _record_error(errors, (scope, "status"), "missing required field")
        return
    if not isinstance(status, str):
        _record_error(errors, (scope, "status"), f"must be string, got {type(status).__name__}")
        return
    if status != OK_STATUS:
        _record_error(errors, (scope, "status"), f"must be '{OK_STATUS}', got {status!r}")


def _require_contract(payload: dict[str, Any], scope: str, expected: str, errors: list[str]) -> None:
    contract = payload.get("contract")
    if not isinstance(contract, str):
        _record_error(errors, (scope, "contract"), f"must be string, got {type(contract).__name__}")
    elif contract != expected:
        _record_error(errors, (scope, "contract"), f"unexpected contract {contract!r}, expected {expected!r}")


def _require_boolean(
    payload: dict[str, Any],
    scope: str,
    alias_pairs: tuple[tuple[str, tuple[str, ...], bool], ...],
    errors: list[str],
) -> None:
    for label, aliases, expected in alias_pairs:
        key, value = _find_field(payload, aliases)
        if key is None:
            _record_error(
                errors,
                (scope,),
                f"missing required key '{label}' (tried aliases: {', '.join(aliases)})",
            )
            continue
        if not isinstance(value, bool):
            _record_error(errors, (scope, key), f"must be bool, got {type(value).__name__}")
        elif value is not expected:
            _record_error(errors, (scope, key), f"must be {expected}, got {value!r}")


def _require_required_keys(
    payload: dict[str, Any],
    scope: str,
    required: dict[str, tuple[type, ...]],
    errors: list[str],
) -> None:
    for field, expected_types in required.items():
        value = payload.get(field, None)
        if value is None and field in payload:
            continue
        if field not in payload:
            _record_error(errors, (scope, field), "missing required key")
            continue
        if not isinstance(value, expected_types):
            _record_error(
                errors,
                (scope, field),
                f"must be {'/'.join(type_.__name__ for type_ in expected_types)}, got {type(value).__name__}",
            )


def _validate_numeric(payload: dict[str, Any], scope: str, errors: list[str]) -> None:
    # Validate that all numeric fields are finite where they appear.
    def walk(node: Any, where: tuple[Any, ...]) -> None:
        if isinstance(node, bool):
            return
        if isinstance(node, float):
            if not math.isfinite(node):
                _record_error(errors, where, f"must be finite, got {node!r}")
            return
        if isinstance(node, int):
            return
        if isinstance(node, list):
            for index, item in enumerate(node):
                walk(item, where + (index,))
            return
        if isinstance(node, dict):
            for key, value in sorted(node.items(), key=lambda item: str(item[0])):
                walk(value, where + (key,))
            return

    walk(payload, (scope,))


def _validate_authority(payload: dict[str, Any], scope: str, errors: list[str]) -> None:
    authority = payload.get("authority")
    if authority is None:
        _record_error(errors, (scope, "authority"), "missing required authority object")
        return
    if not isinstance(authority, dict):
        _record_error(errors, (scope, "authority"), f"must be object, got {type(authority).__name__}")
        return

    for key, expected in REQUIRED_AUTHORITIES.items():
        raw = authority.get(key)
        if key not in authority:
            _record_error(errors, (scope, "authority", key), "missing")
            continue
        if not isinstance(raw, bool):
            _record_error(
                errors,
                (scope, "authority", key),
                f"must be bool, got {type(raw).__name__}",
            )
            continue
        if raw is not expected:
            _record_error(
                errors,
                (scope, "authority", key),
                f"must be {expected}, got {raw}",
            )


def _walk_for_accidental_promotion(node: Any, path: tuple[Any, ...], errors: list[str]) -> None:
    if isinstance(node, dict):
        for key, value in sorted(node.items(), key=lambda item: str(item[0])):
            normalized = _normalize_key(str(key))
            if isinstance(value, bool) and value is True:
                is_theorem_like = "theorem" in normalized
                is_clay_like = "clay" in normalized
                is_promotion_like = "promot" in normalized
                is_promoted_flag = normalized == "promoted"
                if (is_theorem_like or is_clay_like) and is_promotion_like:
                    _record_error(errors, path + (key,), "accidental theorem/Clay promotion flag true")
                if is_promoted_flag:
                    _record_error(errors, path + (key,), "accidental promoted flag true")
            _walk_for_accidental_promotion(value, path + (key,), errors)
        return

    if isinstance(node, list):
        for index, value in enumerate(node):
            _walk_for_accidental_promotion(value, path + (index,), errors)
        return


def _check_stats_shape(stats: dict[str, Any], scope: str, field: str, errors: list[str]) -> None:
    required_stat_keys = ("count", "min", "max", "mean", "sum", "std", "std_err")
    if not isinstance(stats, dict):
        _record_error(errors, (scope, field), f"must be object, got {type(stats).__name__}")
        return
    for key in required_stat_keys:
        if key not in stats:
            continue
        raw = stats[key]
        if isinstance(raw, bool):
            _record_error(errors, (scope, field, key), "must be numeric")
        elif raw is not None and not isinstance(raw, (int, float)):
            _record_error(errors, (scope, field, key), f"must be numeric, got {type(raw).__name__}")
        elif isinstance(raw, float) and not math.isfinite(raw):
            _record_error(errors, (scope, field, key), f"must be finite, got {raw!r}")


def _validate_component(payload: dict[str, Any], errors: list[str]) -> None:
    _require_status(payload, "component", errors)
    _require_contract(payload, "component", EXPECTED_COMPONENT_CONTRACT, errors)

    authority = payload.get("authority")
    if isinstance(authority, dict):
        _validate_authority(payload, "component", errors)
    else:
        errors.append("component:authority: missing required authority object")
        return

    if payload.get("status") != OK_STATUS:
        return

    _require_required_keys(payload, "component", REQUIRED_COMPONENT_KEYS_OK, errors)

    for field in REQUIRED_COMPONENT_NUMERIC:
        value = payload.get(field)
        if value is None and field not in payload:
            _record_error(errors, ("component", field), "missing required numeric field")
            continue
        if isinstance(value, bool) or not isinstance(value, (int, float)):
            _record_error(errors, ("component", field), "must be numeric")
        elif isinstance(value, float) and not math.isfinite(value):
            _record_error(errors, ("component", field), f"must be finite, got {value!r}")

    shape = payload.get("shape")
    if isinstance(shape, list):
        if not shape:
            _record_error(errors, ("component", "shape"), "must be non-empty 3D shape")
        elif any(not isinstance(item, int) for item in shape):
            _record_error(errors, ("component", "shape"), "must contain only integers")

    _check_stats_shape(payload.get("lambda3_stats", {}), "component", "lambda3_stats", errors)
    _check_stats_shape(payload.get("boundary_lambda3_stats", {}), "component", "boundary_lambda3_stats", errors)
    _check_stats_shape(payload.get("tight_band_lambda3_stats", {}), "component", "tight_band_lambda3_stats", errors)


def _validate_f123(payload: dict[str, Any], errors: list[str]) -> None:
    _require_status(payload, "f123", errors)
    _require_contract(payload, "f123", EXPECTED_F123_CONTRACT, errors)

    authority = payload.get("authority")
    if isinstance(authority, dict):
        _validate_authority(payload, "f123", errors)
    else:
        errors.append("f123:authority: missing required authority object")
        return

    if payload.get("status") != OK_STATUS:
        return

    _require_required_keys(payload, "f123", REQUIRED_F123_KEYS_OK, errors)

    for field in REQUIRED_F123_NUMERIC:
        value = payload.get(field)
        if value is None and field not in payload:
            _record_error(errors, ("f123", field), "missing required numeric field")
            continue
        if isinstance(value, bool) or not isinstance(value, (int, float)):
            _record_error(errors, ("f123", field), "must be numeric")
        elif isinstance(value, float) and not math.isfinite(value):
            _record_error(errors, ("f123", field), f"must be finite, got {value!r}")

    shape = payload.get("shape")
    if isinstance(shape, list) and not shape:
        _record_error(errors, ("f123", "shape"), "must be non-empty 3D shape")

    _check_stats_shape(payload.get("density_stats", {}), "f123", "density_stats", errors)
    _check_stats_shape(payload.get("abs_damping_stats", {}), "f123", "abs_damping_stats", errors)

    dominance = payload.get("dominance")
    if isinstance(dominance, dict):
        for field in ("proxy_available", "proxy_count", "min_ratio_sum", "max_ratio_sum", "damping_sum_ratio_reference"):
            value = dominance.get(field)
            if field == "proxy_available":
                if not isinstance(value, bool) and value is not None:
                    _record_error(errors, ("f123", "dominance", field), "must be bool or null")
            elif value is None:
                continue
            elif isinstance(value, bool) or not isinstance(value, (int, float)):
                _record_error(errors, ("f123", "dominance", field), "must be numeric")
            elif isinstance(value, float) and not math.isfinite(value):
                _record_error(errors, ("f123", "dominance", field), f"must be finite, got {value!r}")


def _validate_summary(payload: dict[str, Any], errors: list[str]) -> None:
    # Summary outputs are deterministic receipts; enforce explicit lane flags and ledger fields.
    _require_boolean(payload, "summary", REQUIRED_SUMMARY_FLAGS, errors)
    summary_status = payload.get("status")
    if summary_status is not None and summary_status != OK_STATUS:
        _record_error(errors, ("summary", "status"), f"must be '{OK_STATUS}', got {summary_status!r}")
    if "authority" in payload:
        _validate_authority(payload, "summary", errors)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--component-lambda3-json",
        required=True,
        type=Path,
        help="component-lambda3 diagnostic JSON path",
    )
    parser.add_argument(
        "--f123-absorption-json",
        required=True,
        type=Path,
        help="f123 absorption diagnostic JSON path",
    )
    parser.add_argument(
        "--summary-json",
        required=True,
        type=Path,
        help="NS boundary empirical summary ledger JSON path",
    )
    parser.add_argument(
        "--pretty",
        action="store_true",
        help="pretty-print deterministic JSON output",
    )
    return parser.parse_args()


def main() -> int:
    args = _parse_args()

    errors: list[str] = []
    paths = {
        "component": args.component_lambda3_json,
        "f123": args.f123_absorption_json,
        "summary": args.summary_json,
    }
    payloads: dict[str, dict[str, Any]] = {}

    for label, path in paths.items():
        try:
            payloads[label] = _load_json(path)
        except (OSError, json.JSONDecodeError, ValueError) as exc:
            errors.append(f"{label}: {exc}")

    if "component" in payloads:
        _validate_component(payloads["component"], errors)
    if "f123" in payloads:
        _validate_f123(payloads["f123"], errors)
    if "summary" in payloads:
        _validate_summary(payloads["summary"], errors)

    for label, payload in payloads.items():
        _validate_numeric(payload, label, errors)
        _walk_for_accidental_promotion(payload, (label,), errors)

    result = {
        "contract": CONTRACT,
        "status": OK_STATUS if not errors else FAIL_CLOSED,
        "errors": sorted(set(errors)),
        "inputs": {name: str(path) for name, path in paths.items()},
    }

    print(json.dumps(result, sort_keys=True, indent=2 if args.pretty else None))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
