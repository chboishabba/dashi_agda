#!/usr/bin/env python3
"""Regression checker for Theorem-G cancellation margin output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_boundary_cancellation_margin_regression.py"
CONTRACT = "check_ns_boundary_cancellation_margin_regression"
SOURCE_CONTRACT = "ns_boundary_theoremg_cancellation_margin"
OK_STATUS = "ok"
ERROR_STATUS = "error"
TOLERANCE = 1e-12


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "cancellation_json",
        nargs="?",
        type=Path,
        help="Theorem-G cancellation margin JSON path.",
    )
    parser.add_argument(
        "--cancellation-json",
        type=Path,
        dest="cancellation_json_kw",
        help="Theorem-G cancellation margin JSON path.",
    )
    parser.add_argument(
        "--pretty",
        action="store_true",
        help="Pretty-print JSON output.",
    )
    return parser.parse_args()


def _normalize_path(args: argparse.Namespace) -> Path:
    positional = args.cancellation_json
    flagged = args.cancellation_json_kw
    if positional is not None and flagged is not None:
        raise ValueError("provide exactly one cancellation JSON path, not both positional and --cancellation-json")
    if positional is None and flagged is None:
        raise ValueError("missing required cancellation JSON path")
    return flagged if flagged is not None else positional


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing input file: {path}")
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"top-level payload must be a JSON object: {path}")
    return data


def _coerce_finite_float(label: str, value: Any, path: Path, errors: list[str]) -> float | None:
    if isinstance(value, bool) or value is None:
        errors.append(f"{path}: {label} must be finite numeric, got {value!r}")
        return None
    if isinstance(value, int):
        value_f = float(value)
    elif isinstance(value, float):
        value_f = value
    elif isinstance(value, str):
        try:
            value_f = float(value)
        except ValueError:
            errors.append(f"{path}: {label} must be finite numeric, got {value!r}")
            return None
    else:
        errors.append(f"{path}: {label} must be finite numeric, got {type(value).__name__}")
        return None

    if not math.isfinite(value_f):
        errors.append(f"{path}: {label} must be finite, got {value!r}")
        return None

    return value_f


def _coerce_bool(label: str, value: Any, path: Path, errors: list[str]) -> bool | None:
    if not isinstance(value, bool):
        errors.append(f"{path}: {label} must be bool, got {type(value).__name__}")
        return None
    return value


def _check_authority(payload: dict[str, Any], path: Path, errors: list[str]) -> None:
    authority = payload.get("authority")
    if authority is None:
        errors.append(f"{path}: missing required 'authority' object")
        return
    if not isinstance(authority, dict):
        errors.append(f"{path}: authority must be object, got {type(authority).__name__}")
        return
    if not authority:
        errors.append(f"{path}: authority object is empty")


def _normalize_key(value: str) -> str:
    return "".join(character for character in value.lower() if character.isalnum())


def _is_promotion_flag(key: str) -> bool:
    normalized = _normalize_key(key)
    return "promotion" in normalized or "promoting" in normalized or "promoted" in normalized


def _check_payload(payload: dict[str, Any], path: Path) -> tuple[list[str], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []

    _check_authority(payload, path, errors)

    for key in ("O", "R", "C", "S", "L", "P", "G", "F"):
        value = payload.get(key)
        if not isinstance(value, str) or not value.strip():
            errors.append(f"{path}: missing or empty O/R/C/S/L/P/G/F field '{key}'")

    contract = payload.get("contract")
    if not isinstance(contract, str):
        errors.append(f"{path}: contract missing or not string")
    elif contract != SOURCE_CONTRACT:
        errors.append(f"{path}: contract must be '{SOURCE_CONTRACT}', got {contract!r}")

    delta1 = _coerce_finite_float("delta1", payload.get("delta1"), path, errors)
    if isinstance(delta1, float):
        if delta1 <= 0.0:
            errors.append(f"{path}: delta1 must be finite positive, got {delta1:.17g}")

    mu_cancellation = _coerce_finite_float(
        "mu_cancellation", payload.get("mu_cancellation"), path, errors
    )
    if isinstance(delta1, float) and isinstance(mu_cancellation, float):
        if not math.isclose(mu_cancellation, delta1, rel_tol=TOLERANCE, abs_tol=TOLERANCE):
            errors.append(
                f"{path}: mu_cancellation mismatch: expected {delta1:.17g}, got {mu_cancellation:.17g}"
            )

    threshold = _coerce_finite_float("threshold", payload.get("threshold"), path, errors)
    if threshold is not None and threshold != 0.0:
        errors.append(f"{path}: threshold must be 0, got {threshold!r}")

    margin_positive = _coerce_bool("margin_positive", payload.get("margin_positive"), path, errors)
    if isinstance(delta1, float) and isinstance(margin_positive, bool):
        if margin_positive is not (delta1 > 0.0):
            errors.append(
                f"{path}: margin_positive={margin_positive} inconsistent with delta1>0 ({delta1 > 0.0})"
            )

    status = payload.get("status")
    if status is None:
        warnings.append(f"{path}: missing status")
    elif not isinstance(status, str):
        warnings.append(f"{path}: status should be a string, got {type(status).__name__}")

    # Require that all promotion-like booleans are false.
    for key, value in payload.items():
        if _is_promotion_flag(key):
            if not isinstance(value, bool):
                continue
            if value:
                errors.append(f"{path}: promotion flag '{key}' must be false")

    for required in ("clay_promotion", "collapse_impossible", "h_delta1_promoting"):
        if required not in payload:
            warnings.append(f"{path}: missing expected non-promotion field '{required}'")
        else:
            value = payload[required]
            if isinstance(value, bool) and value:
                errors.append(f"{path}: {required} must be false")

    f123_signed = payload.get("f123_damping_sum_signed")
    if f123_signed is None:
        f123_signed = payload.get("damping_sum_signed")
    if f123_signed is not None:
        f123_signed_f = _coerce_finite_float("f123 signed damping", f123_signed, path, errors)
        if f123_signed_f is not None and f123_signed_f > 0.0:
            errors.append(
                f"{path}: f123 signed damping sum must be <= 0, got {f123_signed_f:.17g}"
            )

    return errors, warnings


def main() -> int:
    pretty = False
    try:
        args = _parse_args()
        pretty = bool(args.pretty)
        path = _normalize_path(args)
    except (ValueError, OSError) as exc:
        result = {
            "contract": CONTRACT,
            "status": ERROR_STATUS,
            "errors": [str(exc)],
            "warnings": [],
            "inputs": {"cancellation_json": None},
            "changed_files": [],
            "O": "Regression checker for Theorem-G cancellation margin JSON output.",
            "R": "Verify arithmetic and gate flags for cancellation margin artifacts.",
            "C": SCRIPT_NAME,
            "S": "Fail closed on required field/type invariant violations.",
            "L": "Only errors flip status to error; warnings do not fail.",
            "P": "FAIL_CLOSED_NS_BOUNDARY_CANCELLATION_MARGIN_REGRESSION",
            "G": "No theorem, Clay, or promotion claim is introduced by this checker.",
            "F": "This checker only performs regression validation of empirical cancellation margin fields.",
        }
        print(json.dumps(result, sort_keys=True, indent=2 if pretty else None))
        return 1

    errors: list[str] = []
    warnings: list[str] = []
    try:
        payload = _load_json(path)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        errors.append(f"{path}: {exc}")
        status = ERROR_STATUS
    else:
        check_errors, check_warnings = _check_payload(payload, path)
        errors.extend(check_errors)
        warnings.extend(check_warnings)
        status = ERROR_STATUS if errors else OK_STATUS

    result = {
        "contract": CONTRACT,
        "status": status,
        "errors": sorted(set(errors)),
        "warnings": sorted(set(warnings)),
        "inputs": {"cancellation_json": str(path)},
        "changed_files": [str(path)],
        "O": "Regression checker for Theorem-G cancellation margin JSON output.",
        "R": "Verify arithmetic and gate flags for cancellation margin artifacts.",
        "C": SCRIPT_NAME,
        "S": "Validate authority, contract, delta1/mu_cancellation consistency, and non-promotion flags.",
        "L": "Only explicit validation failures are treated as hard errors.",
        "P": "FAIL_CLOSED_NS_BOUNDARY_CANCELLATION_MARGIN_REGRESSION",
        "G": "No theorem, Clay, or promotion claim is introduced by this checker.",
        "F": "This checker is regression-only; analytic or theorem status is not inferred.",
    }
    print(json.dumps(result, sort_keys=True, indent=2 if args.pretty else None))
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
