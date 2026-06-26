#!/usr/bin/env python3
"""Regression checker for weighted lambda2 carrier quantile JSON."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_weighted_lambda2_carrier_quantile_regression.py"
CONTRACT = "check_ns_weighted_lambda2_carrier_quantile_regression"
OK_STATUS = "ok"
ERROR_STATUS = "error"
EXPECTED_FRAME_COUNT = 13
EXPECTED_TARGET_FRACTIONS = (0.05, 0.10, 0.25, 0.50, 0.75, 0.90)
CHECK_CARD_KEYS = ("O", "R", "C", "S", "L", "P", "G", "F")

FRAME_COUNT_KEYS = (
    "frame_count",
    "available_frame_count",
    "processed_frame_count",
    "row_count",
)

TARGET_FRACTION_KEYS = (
    "target_fractions",
    "target_fraction",
    "fractions",
    "fraction_targets",
    "fraction_levels",
    "quantiles",
    "quantile_fractions",
    "quantile_levels",
)

AGGREGATE_KEYS = (
    "aggregate",
    "aggregate_stats",
    "summary",
    "stats",
)

AUTHORITY_ALLOW_TRUE = {"candidateonly", "empiricalnonpromoting", "nonpromoting", "diagnosticonly"}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "json_path",
        nargs="?",
        type=Path,
        help="Path to the weighted lambda2 carrier quantile regression JSON.",
    )
    parser.add_argument(
        "--json-path",
        dest="json_path_kw",
        type=Path,
        help="Path to the weighted lambda2 carrier quantile regression JSON.",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=None,
        help="Optional output receipt path.",
    )
    return parser.parse_args()


def _normalize_key(value: str) -> str:
    return "".join(character.lower() for character in value if character.isalnum())


def _join_path(path: tuple[Any, ...]) -> str:
    if not path:
        return ""
    parts: list[str] = []
    for entry in path:
        if isinstance(entry, int):
            parts.append(f"[{entry}]")
        else:
            if parts:
                parts.append(".")
            parts.append(str(entry))
    return "".join(parts)


def _record_error(errors: list[str], path: tuple[Any, ...], message: str) -> None:
    prefix = _join_path(path)
    errors.append(f"{prefix}: {message}" if prefix else message)


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing input file: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"top-level JSON payload is not an object: {path}")
    return payload


def _find_field(payload: dict[str, Any], aliases: tuple[str, ...]) -> tuple[str | None, Any | None]:
    for alias in aliases:
        if alias in payload:
            return alias, payload[alias]
    normalized_aliases = {_normalize_key(alias): alias for alias in aliases}
    for key, value in payload.items():
        if isinstance(key, str) and _normalize_key(key) in normalized_aliases:
            return key, value
    return None, None


def _is_finite_number(value: Any) -> bool:
    if isinstance(value, bool):
        return False
    if isinstance(value, int):
        return True
    if isinstance(value, float):
        return math.isfinite(value)
    return False


def _coerce_fraction(value: Any) -> float | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, (int, float)):
        value_f = float(value)
        if math.isfinite(value_f):
            return value_f
    if isinstance(value, str):
        try:
            value_f = float(value)
        except ValueError:
            return None
        if math.isfinite(value_f):
            return value_f
    return None


def _collect_fractions(node: Any, path: tuple[Any, ...], fractions: dict[float, str]) -> None:
    if isinstance(node, dict):
        for key, value in node.items():
            if isinstance(key, str):
                normalized = _normalize_key(key)
                if normalized in {"fraction", "frac", "targetfraction", "eps", "epsilon"}:
                    fraction = _coerce_fraction(value)
                    if fraction is not None:
                        fractions.setdefault(fraction, _join_path(path + (key,)))
                elif normalized in {"targetfraction", "targetfractions", "epsneeded", "epsilonneeded"}:
                    fraction = _coerce_fraction(value)
                    if fraction is not None:
                        fractions.setdefault(fraction, _join_path(path + (key,)))
                elif normalized in {"fractions", "targetfractions", "targetfractionlevels"} and isinstance(value, (list, tuple)):
                    for index, item in enumerate(value):
                        fraction = _coerce_fraction(item)
                        if fraction is not None:
                            fractions.setdefault(fraction, _join_path(path + (key, index)))
            _collect_fractions(value, path + (key,), fractions)
        return
    if isinstance(node, (list, tuple)):
        for index, item in enumerate(node):
            fraction = _coerce_fraction(item)
            if fraction is not None:
                fractions.setdefault(fraction, _join_path(path + (index,)))
            _collect_fractions(item, path + (index,), fractions)


def _collect_eps_needed_issues(
    node: Any,
    path: tuple[Any, ...],
    errors: list[str],
    active: bool = False,
) -> tuple[int, bool]:
    count = 0
    valid = True
    if isinstance(node, dict):
        for key, value in node.items():
            next_active = active or (isinstance(key, str) and "epsneeded" in _normalize_key(key))
            child_count, child_valid = _collect_eps_needed_issues(value, path + (key,), errors, next_active)
            count += child_count
            valid = valid and child_valid
        return count, valid
    if isinstance(node, (list, tuple)):
        for index, item in enumerate(node):
            child_count, child_valid = _collect_eps_needed_issues(item, path + (index,), errors, active)
            count += child_count
            valid = valid and child_valid
        return count, valid
    if active and isinstance(node, (int, float, str)) and not isinstance(node, bool):
        count = 1
        try:
            value = float(node)
        except ValueError:
            _record_error(errors, path, f"must be numeric, got {node!r}")
            return count, False
        if not math.isfinite(value):
            _record_error(errors, path, f"must be finite, got {node!r}")
            valid = False
        elif value < 0.0:
            _record_error(errors, path, f"must be nonnegative, got {node!r}")
            valid = False
    return count, valid


def _validate_status(payload: dict[str, Any], errors: list[str]) -> None:
    status = payload.get("status")
    if not isinstance(status, str):
        _record_error(errors, ("status",), f"must be string, got {type(status).__name__}")
    elif status != OK_STATUS:
        _record_error(errors, ("status",), f"must be {OK_STATUS!r}, got {status!r}")


def _validate_frame_count(payload: dict[str, Any], errors: list[str]) -> int | None:
    observed: int | None = None
    for key in FRAME_COUNT_KEYS:
        if key not in payload:
            continue
        value = payload[key]
        if isinstance(value, bool) or not isinstance(value, int):
            _record_error(errors, (key,), f"must be a nonnegative integer, got {value!r}")
            continue
        if value < 0:
            _record_error(errors, (key,), f"must be nonnegative, got {value}")
            continue
        observed = value if observed is None else observed
        if value != EXPECTED_FRAME_COUNT:
            _record_error(errors, (key,), f"must be {EXPECTED_FRAME_COUNT}, got {value}")

    for key in ("frames", "rows", "frame_rows", "frame_records", "records"):
        value = payload.get(key)
        if isinstance(value, list):
            if len(value) != EXPECTED_FRAME_COUNT:
                _record_error(errors, (key,), f"length {len(value)} must be {EXPECTED_FRAME_COUNT}")
            observed = EXPECTED_FRAME_COUNT
        elif value is not None and not isinstance(value, (dict, str)):
            _record_error(errors, (key,), f"must be a list when present, got {type(value).__name__}")

    return observed


def _validate_target_fractions(payload: dict[str, Any], errors: list[str]) -> list[float]:
    found_alias, found_value = _find_field(payload, ("targets",) + TARGET_FRACTION_KEYS)

    fractions: list[float] = []
    if found_alias is not None:
        if isinstance(found_value, dict):
            for key, value in found_value.items():
                fraction = _coerce_fraction(key)
                if fraction is None:
                    fraction = _coerce_fraction(value)
                if fraction is not None:
                    fractions.append(fraction)
        elif isinstance(found_value, (list, tuple)):
            for item in found_value:
                fraction = _coerce_fraction(item)
                if fraction is not None:
                    fractions.append(fraction)
        else:
            fraction = _coerce_fraction(found_value)
            if fraction is not None:
                fractions.append(fraction)
        if not fractions:
            _record_error(errors, (found_alias,), "must contain numeric target fractions")
    else:
        _record_error(
            errors,
            tuple(),
            "missing required target fractions (expected top-level targets/target_fractions/fractions)",
        )

    fractions = sorted(set(fractions))
    missing = [target for target in EXPECTED_TARGET_FRACTIONS if all(abs(target - fraction) > 1e-12 for fraction in fractions)]
    if missing:
        _record_error(errors, ("target_fractions",), f"missing required fractions {missing!r}")
    return fractions


def _validate_aggregate(payload: dict[str, Any], errors: list[str]) -> str | None:
    key, value = _find_field(payload, AGGREGATE_KEYS)
    if key is None:
        _record_error(
            errors,
            tuple(),
            "missing aggregate stats object (expected one of aggregate/aggregate_stats/summary/stats)",
        )
        return None
    if not isinstance(value, dict):
        _record_error(errors, (key,), f"must be an object, got {type(value).__name__}")
        return key
    return key


def _validate_authority(payload: dict[str, Any], errors: list[str]) -> bool:
    authority = payload.get("authority")
    if not isinstance(authority, dict):
        _record_error(errors, ("authority",), f"must be an object, got {type(authority).__name__}")
        return False

    authority_false = True
    for key, value in authority.items():
        if not isinstance(key, str):
            continue
        normalized = _normalize_key(key)
        if isinstance(value, bool):
            if normalized in AUTHORITY_ALLOW_TRUE:
                continue
            if value:
                _record_error(errors, ("authority", key), "must be false")
                authority_false = False
        elif isinstance(value, (int, float)) and not _is_finite_number(value):
            _record_error(errors, ("authority", key), f"must be finite, got {value!r}")
            authority_false = False
        elif not isinstance(value, (str, list, tuple, dict, type(None))):
            _record_error(errors, ("authority", key), f"must be boolean or structured metadata, got {type(value).__name__}")
            authority_false = False

    return authority_false


def _validate_promotion_flags(payload: dict[str, Any], errors: list[str]) -> None:
    def walk(node: Any, path: tuple[Any, ...]) -> None:
        if isinstance(node, dict):
            for key, value in node.items():
                if isinstance(key, str):
                    normalized = _normalize_key(key)
                    if isinstance(value, bool) and (
                        "promotion" in normalized
                        or "promoting" in normalized
                        or "promoted" in normalized
                        or normalized in {"clayauthority", "theoremauthority", "truthauthority", "runtimeauthority"}
                    ):
                        if normalized in {"candidateonly", "empiricalnonpromoting", "nonpromoting", "diagnosticonly"}:
                            pass
                        elif value:
                            _record_error(errors, path + (key,), "must be false")
                walk(value, path + (key,))
            return
        if isinstance(node, (list, tuple)):
            for index, value in enumerate(node):
                walk(value, path + (index,))

    walk(payload, tuple())


def main() -> int:
    args = _parse_args()
    json_path = args.json_path_kw or args.json_path

    if json_path is None:
        result = {
            "contract": CONTRACT,
            "status": ERROR_STATUS,
            "errors": ["missing required quantile JSON path"],
            "warnings": [],
            "changed_files": [],
            "O": "Regression checker for weighted lambda2 carrier quantile JSON.",
            "R": "validate status, frame coverage, target fractions, eps-needed values, aggregate stats, and authority flags",
            "C": SCRIPT_NAME,
            "S": "Fail closed on malformed regression JSON.",
            "L": "Status, 13 frames, required target fractions, finite eps-needed values, aggregate stats, and false authority are mandatory.",
            "P": "FAIL_CLOSED_NS_WEIGHTED_LAMBDA2_CARRIER_QUANTILE_REGRESSION",
            "G": "No theorem, Clay, or promotion claim is inferred.",
            "F": "This checker only validates a generated quantile regression artifact.",
        }
        print(json.dumps(result, sort_keys=True, separators=(",", ":")))
        return 1

    errors: list[str] = []
    warnings: list[str] = []
    changed_files = [str(json_path)]
    if args.output_json is not None:
        changed_files.append(str(args.output_json))

    try:
        payload = _load_json(json_path)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        errors.append(f"{json_path}: {exc}")
        payload = {}

    if payload:
        _validate_status(payload, errors)
        _validate_frame_count(payload, errors)
        target_fractions = _validate_target_fractions(payload, errors)
        _validate_aggregate(payload, errors)
        authority_false = _validate_authority(payload, errors)
        _validate_promotion_flags(payload, errors)
        eps_needed_count, eps_needed_ok = _collect_eps_needed_issues(payload, tuple(), errors)
        if eps_needed_count == 0:
            _record_error(errors, tuple(), "missing required eps-needed values")
    else:
        target_fractions = []
        authority_false = False
        eps_needed_count = 0
        eps_needed_ok = False

    status = OK_STATUS if not errors else ERROR_STATUS
    result: dict[str, Any] = {
        "contract": CONTRACT,
        "status": status,
        "errors": sorted(set(errors)),
        "warnings": sorted(set(warnings)),
        "changed_files": changed_files,
        "authority_false": authority_false,
        "validation": {
            "frame_count": EXPECTED_FRAME_COUNT,
            "target_fractions": target_fractions,
            "expected_target_fractions": list(EXPECTED_TARGET_FRACTIONS),
            "eps_needed_count": eps_needed_count,
            "eps_needed_ok": eps_needed_count > 0 and eps_needed_ok,
        },
        "O": "Regression checker for weighted lambda2 carrier quantile JSON.",
        "R": "validate status, frame coverage, target fractions, eps-needed values, aggregate stats, and authority flags",
        "C": SCRIPT_NAME,
        "S": "Fail closed on malformed regression JSON.",
        "L": "Status, 13 frames, required target fractions, finite eps-needed values, aggregate stats, and false authority are mandatory.",
        "P": "FAIL_CLOSED_NS_WEIGHTED_LAMBDA2_CARRIER_QUANTILE_REGRESSION",
        "G": "No theorem, Clay, or promotion claim is inferred.",
        "F": "This checker only validates a generated quantile regression artifact.",
    }

    output = json.dumps(result, sort_keys=True, separators=(",", ":"))
    if args.output_json is not None:
        try:
            args.output_json.write_text(output + "\n", encoding="utf-8")
        except OSError as exc:
            errors.append(f"{args.output_json}: {exc}")
            status = ERROR_STATUS
            result["status"] = status
            result["errors"] = sorted(set(errors))
            output = json.dumps(result, sort_keys=True, separators=(",", ":"))

    print(output)

    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
