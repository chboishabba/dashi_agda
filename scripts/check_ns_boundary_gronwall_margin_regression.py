#!/usr/bin/env python3
"""Regression checker for corrected Theorem-G Gronwall margin JSON artifacts."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


CONTRACT = "check_ns_boundary_gronwall_margin_regression"
SCRIPT_NAME = "scripts/check_ns_boundary_gronwall_margin_regression.py"
OK_STATUS = "ok"
ERROR_STATUS = "error"
MARGIN_TOLERANCE = 1e-12

REQUIRED_AUTHORITIES = (
    "candidate_only",
    "empirical_non_promoting",
    "truth_authority",
    "theorem_authority",
    "clay_authority",
    "runtime_authority",
    "promoted",
)

NON_PROMOTION_KEYS = (
    "clay_promotion",
    "collapse_impossible",
    "h_delta1_promoting",
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--margin-json",
        action="append",
        type=Path,
        required=True,
        help="Corrected margin JSON artifact (repeatable).",
    )
    parser.add_argument(
        "--timeseries-json",
        type=Path,
        default=None,
        help="Optional margin timeseries summary JSON artifact.",
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
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"payload is not a JSON object: {path}")
    return data


def _coerce_finite_float(
    path: str,
    payload: dict[str, Any],
    key: str,
    errors: list[str],
) -> float | None:
    if key not in payload:
        errors.append(f"{path}: missing required field '{key}'")
        return None

    value = payload[key]
    if isinstance(value, bool):
        errors.append(f"{path}: {key} must be numeric, got bool")
        return None
    if isinstance(value, int):
        value_f = float(value)
    elif isinstance(value, float):
        value_f = value
    elif isinstance(value, str):
        try:
            value_f = float(value)
        except ValueError:
            errors.append(f"{path}: {key} must be numeric, got {value!r}")
            return None
    else:
        errors.append(f"{path}: {key} must be numeric, got {type(value).__name__}")
        return None

    if not math.isfinite(value_f):
        errors.append(f"{path}: {key} must be finite, got {value!r}")
        return None

    return value_f


def _coerce_optional_finite_float(
    path: str,
    payload: dict[str, Any],
    keys: tuple[str, ...],
    errors: list[str],
) -> float | None:
    for key in keys:
        if key not in payload:
            continue
        value = payload[key]
        if value is None:
            return None
        if isinstance(value, bool):
            errors.append(f"{path}: {key} must be numeric or null, got bool")
            return None
        if isinstance(value, int):
            return float(value)
        if isinstance(value, float):
            if not math.isfinite(value):
                errors.append(f"{path}: {key} must be finite, got {value!r}")
                return None
            return value
        if isinstance(value, str):
            try:
                value_f = float(value)
            except ValueError:
                errors.append(f"{path}: {key} must be numeric or null, got {value!r}")
                return None
            if not math.isfinite(value_f):
                errors.append(f"{path}: {key} must be finite, got {value!r}")
                return None
            return value_f

        errors.append(f"{path}: {key} must be numeric or null, got {type(value).__name__}")
        return None
    return None


def _coerce_bool(payload_path: str, payload: dict[str, Any], key: str, errors: list[str]) -> bool | None:
    if key not in payload:
        errors.append(f"{payload_path}: missing required flag '{key}'")
        return None
    value = payload[key]
    if not isinstance(value, bool):
        errors.append(f"{payload_path}: {key} must be bool, got {type(value).__name__}")
        return None
    return value


def _validate_authority(payload_path: str, payload: dict[str, Any], errors: list[str], warnings: list[str]) -> None:
    authority = payload.get("authority")
    if authority is None:
        errors.append(f"{payload_path}: missing authority object")
        return
    if not isinstance(authority, dict):
        errors.append(f"{payload_path}: authority must be object, got {type(authority).__name__}")
        return

    for key in REQUIRED_AUTHORITIES:
        if key not in authority:
            errors.append(f"{payload_path}: authority missing '{key}'")
        elif not isinstance(authority[key], bool):
            errors.append(f"{payload_path}: authority['{key}'] must be bool, got {type(authority[key]).__name__}")

    # keep a soft warning if authority is present but marked as promoted/theorem/Clay
    # to prevent accidental status drift.
    promoted_like = {
        "clay_authority",
        "theorem_authority",
        "promoted",
        "truth_authority",
        "runtime_authority",
    }
    for key in promoted_like:
        value = authority.get(key)
        if value is True:
            warnings.append(f"{payload_path}: authority flag '{key}' is true")


def _validate_margin_file(
    payload_path: Path,
    payload: dict[str, Any],
    errors: list[str],
    warnings: list[str],
) -> None:
    path_label = str(payload_path)

    _validate_authority(path_label, payload, errors, warnings)

    delta1 = _coerce_finite_float(path_label, payload, "delta1", errors)
    mu = _coerce_finite_float(path_label, payload, "mu", errors)
    margin_positive = _coerce_bool(path_label, payload, "margin_positive", errors)

    if isinstance(delta1, (float, int)):
        if delta1 <= 0.0:
            errors.append(f"{path_label}: delta1 must be positive")
        if isinstance(mu, (float, int)):
            expected_mu = 2.0 * delta1 - 1.0 / delta1
            if not math.isclose(mu, expected_mu, rel_tol=MARGIN_TOLERANCE, abs_tol=MARGIN_TOLERANCE):
                errors.append(
                    f"{path_label}: mu mismatch: expected 2*delta1 - 1/delta1={expected_mu:.17g}, got {mu:.17g}"
                )

    if isinstance(margin_positive, bool) and isinstance(mu, (float, int)):
        if margin_positive is not (mu > 0.0):
            errors.append(
                f"{path_label}: margin_positive={margin_positive} is inconsistent with mu>0 ({mu > 0.0})"
            )

    for key in NON_PROMOTION_KEYS:
        value = payload.get(key)
        if value is None:
            warnings.append(f"{path_label}: missing expected non-promotion flag '{key}'")
            continue
        if not isinstance(value, bool):
            errors.append(f"{path_label}: {key} must be bool, got {type(value).__name__}")
            continue
        if value:
            errors.append(f"{path_label}: {key} must remain false")

    f123_signed = _coerce_optional_finite_float(
        path_label,
        payload,
        ("f123_damping_sum_signed", "damping_sum_signed"),
        errors,
    )
    if f123_signed is not None and f123_signed > 0.0:
        errors.append(f"{path_label}: f123 signed damping sum must be <= 0, got {f123_signed}")

    status = payload.get("status")
    if status is not None and status != OK_STATUS:
        warnings.append(f"{path_label}: status is {status!r}, expected 'ok'")

    if payload.get("schema_version") is None:
        warnings.append(f"{path_label}: missing schema_version")


def _validate_timeseries_file(
    payload_path: Path,
    payload: dict[str, Any],
    warnings: list[str],
    errors: list[str],
) -> None:
    path_label = str(payload_path)
    _validate_authority(path_label, payload, errors, warnings)

    status = payload.get("status")
    if status is not None and status not in {OK_STATUS}:
        warnings.append(f"{path_label}: status is {status!r}, expected 'ok'")

    promotion = payload.get("promotion")
    if isinstance(promotion, dict):
        for key, value in sorted(promotion.items(), key=lambda item: str(item[0])):
            if key in {"full_clay_ns_solved", "clay_navier_stokes_promoted", "clay_promoted", "theorem_promoted"}:
                if value is True:
                    errors.append(
                        f"{path_label}: promotion flag '{key}' must be false, got true"
                    )
            if not isinstance(value, bool) and value is not None:
                warnings.append(
                    f"{path_label}: promotion '{key}' should be bool, got {type(value).__name__}"
                )


def _build_result(
    margin_paths: list[Path],
    timeseries_path: Path | None,
    errors: list[str],
    warnings: list[str],
) -> dict[str, Any]:
    changed_files: list[str] = [str(path) for path in margin_paths]
    if timeseries_path is not None:
        changed_files.append(str(timeseries_path))

    status = OK_STATUS if not errors else ERROR_STATUS
    result: dict[str, Any] = {
        "contract": CONTRACT,
        "status": status,
        "errors": sorted(set(errors)),
        "warnings": sorted(set(warnings)),
        "inputs": {
            "margin_json": [str(path) for path in margin_paths],
            "timeseries_json": None if timeseries_path is None else str(timeseries_path),
        },
        "changed_files": sorted(set(changed_files)),
        "O": "Regression check for corrected Gronwall margin artifacts and optional timeseries summaries.",
        "R": "Enforce finite corrected margin invariants and non-promotion constraints before allowing promotion claims.",
        "C": SCRIPT_NAME,
        "S": "Validate authority, compute mu consistency, and enforce signed-F123 and non-promotion flags.",
        "L": "Fail-closed: any inconsistency in required invariants is treated as an error.",
        "P": "FAIL_CLOSED_NS_BOUNDARY_GRONWALL_MARGIN_REGRESSION",
        "G": "No theorem, Clay, or promotion claims are asserted by this regression script.",
        "F": "This is empirical regression hygiene only; analytic closure and promotion logic stay false unless validated elsewhere.",
    }
    return result


def main() -> int:
    args = _parse_args()
    errors: list[str] = []
    warnings: list[str] = []

    for margin_path in args.margin_json:
        try:
            payload = _load_json(margin_path)
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            errors.append(f"{margin_path}: {exc}")
            continue
        _validate_margin_file(margin_path, payload, errors, warnings)

    if args.timeseries_json is not None:
        try:
            timeseries_payload = _load_json(args.timeseries_json)
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            errors.append(f"{args.timeseries_json}: {exc}")
        else:
            _validate_timeseries_file(args.timeseries_json, timeseries_payload, warnings, errors)

    result = _build_result(args.margin_json, args.timeseries_json, errors, warnings)
    print(json.dumps(result, sort_keys=True, indent=2 if args.pretty else None))
    return 0 if result["status"] == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
