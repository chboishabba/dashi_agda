#!/usr/bin/env python3
"""Project cancellation-margin upgrade from corrected Gronwall margin JSON."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_boundary_theoremg_cancellation_margin.py"
CONTRACT = "ns_boundary_theoremg_cancellation_margin"
SCHEMA_VERSION = "1.0.0"
ROUTE_DECISION = "FAIL_CLOSED_NS_BOUNDARY_CANCELLATION_MARGIN"
DEFAULT_OUTPUT = Path("outputs/ns_boundary_theoremg_cancellation_margin.json")

OK_STATUS = "ok"
WARNING_STATUS = "warning"
ERROR_STATUS = "error"

DEFAULT_AUTHORITY: dict[str, bool] = {
    "candidate_only": True,
    "empirical_non_promoting": True,
    "truth_authority": False,
    "theorem_authority": False,
    "clay_authority": False,
    "runtime_authority": False,
    "promoted": False,
}

PROMOTION_KEYS: tuple[str, ...] = (
    "h_delta1_promoting",
    "clay_promotion",
    "full_clay_ns_solved",
    "clay_navier_stokes_promoted",
    "clay_promoted",
    "theorem_promoted",
    "proof_blocking",
    "collapse_impossible",
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--margin-json",
        type=Path,
        required=True,
        help="Input corrected margin artifact from the Theorem-G corrected Gronwall pass.",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Output JSON path.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output.")
    return parser.parse_args()


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing input file: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"input JSON must be an object: {path}")
    return payload


def _coerce_finite_float(path: Path, value: Any, field: str, errors: list[str]) -> float | None:
    if isinstance(value, bool) or value is None:
        errors.append(f"{path}: {field} must be finite numeric, got {value!r}")
        return None

    if isinstance(value, int):
        value_f = float(value)
    elif isinstance(value, float):
        value_f = value
    elif isinstance(value, str):
        try:
            value_f = float(value.strip())
        except ValueError:
            errors.append(f"{path}: {field} must be finite numeric, got {value!r}")
            return None
    else:
        errors.append(f"{path}: {field} must be finite numeric, got {type(value).__name__}")
        return None

    if not math.isfinite(value_f):
        errors.append(f"{path}: {field} must be finite, got {value!r}")
        return None

    return float(value_f)


def _coerce_optional_float(path: Path, value: Any, field: str, warnings: list[str]) -> float | None:
    if value is None:
        return None
    if isinstance(value, bool):
        warnings.append(f"{path}: {field} should be numeric, got bool")
        return None
    if isinstance(value, int):
        value_f = float(value)
    elif isinstance(value, float):
        value_f = value
    elif isinstance(value, str):
        try:
            value_f = float(value.strip())
        except ValueError:
            warnings.append(f"{path}: {field} should be numeric, got {value!r}")
            return None
    else:
        warnings.append(f"{path}: {field} should be numeric, got {type(value).__name__}")
        return None

    if not math.isfinite(value_f):
        warnings.append(f"{path}: {field} should be finite, got {value!r}")
        return None

    return float(value_f)


def _collect_source_warnings(payload: dict[str, Any], warnings: list[str]) -> None:
    source_warnings = payload.get("warnings")
    if source_warnings is None:
        return
    if isinstance(source_warnings, list):
        for item in source_warnings:
            if isinstance(item, str):
                warnings.append(item)
            else:
                warnings.append("source_non_string_warning")
        return
    warnings.append("source_warnings_not_list")


def _extract_authority(payload: dict[str, Any], warnings: list[str]) -> dict[str, Any]:
    authority = payload.get("authority")
    if isinstance(authority, dict):
        return dict(authority)
    warnings.append("authority_missing_or_not_object")
    return dict(DEFAULT_AUTHORITY)


def _commutator_available(payload: dict[str, Any], warnings: list[str]) -> bool:
    for key in ("commutator_measurement_available", "commutator_comparison_measured"):
        value = payload.get(key)
        if isinstance(value, bool):
            if not value:
                warnings.append("no_positive_commutator_measurement")
            return value
    warnings.append("no_positive_commutator_measurement")
    return False


def _extract_f123(payload: dict[str, Any], path: Path, warnings: list[str]) -> tuple[float | None, float | None]:
    signed_raw = payload.get("f123_damping_sum_signed", payload.get("damping_sum_signed"))
    abs_raw = payload.get("f123_damping_sum_abs", payload.get("damping_sum_abs"))
    signed = _coerce_optional_float(path, signed_raw, "f123_damping_sum_signed", warnings)
    absolute = _coerce_optional_float(path, abs_raw, "f123_damping_sum_abs", warnings)
    return signed, absolute


def _build_payload(input_path: Path, output_path: Path) -> tuple[dict[str, Any], int]:
    errors: list[str] = []
    warnings: list[str] = []

    margin_payload = _read_json(input_path)
    _collect_source_warnings(margin_payload, warnings)

    authority = _extract_authority(margin_payload, warnings)

    if not isinstance(margin_payload.get("status"), str):
        warnings.append("source_status_missing_or_not_string")
    source_contract = margin_payload.get("contract")
    if not isinstance(source_contract, str):
        warnings.append("source_contract_missing_or_not_string")
    source_route = margin_payload.get("route_decision", margin_payload.get("route"))
    if source_route is not None and not isinstance(source_route, str):
        warnings.append("source_route_not_string")

    source_inputs = margin_payload.get("inputs") if isinstance(margin_payload.get("inputs"), dict) else None
    source_provenance = (
        margin_payload.get("provenance") if isinstance(margin_payload.get("provenance"), dict) else None
    )

    delta1 = _coerce_finite_float(input_path, margin_payload.get("delta1"), "delta1", errors)
    if delta1 is not None and delta1 <= 0.0:
        errors.append(f"{input_path}: delta1 must be > 0, got {delta1:.17g}")

    for key in PROMOTION_KEYS:
        if key not in margin_payload:
            continue
        value = margin_payload[key]
        if isinstance(value, bool):
            if value:
                errors.append(f"{input_path}: promotion flag '{key}' must be false")
        else:
            warnings.append(f"{input_path}: promotion flag '{key}' expected bool, got {type(value).__name__}")

    measurement_available = _commutator_available(margin_payload, warnings)
    comparison_measured = margin_payload.get("commutator_comparison_measured")
    if not isinstance(comparison_measured, bool):
        comparison_measured = measurement_available
    comparison_proxy_unavailable = margin_payload.get(
        "commutator_comparison_proxy_unavailable", not measurement_available
    )

    f123_signed, f123_abs = _extract_f123(margin_payload, input_path, warnings)
    source_f123_json = None
    if isinstance(source_inputs, dict):
        json_candidate = source_inputs.get("f123_json")
        if isinstance(json_candidate, str):
            source_f123_json = json_candidate

    status = ERROR_STATUS if errors else WARNING_STATUS if warnings else OK_STATUS

    payload: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "contract": CONTRACT,
        "status": status,
        "script": SCRIPT_NAME,
        "route_decision": ROUTE_DECISION,
        "authority": authority,
        "provenance": {
            "margin_json": {
                "path": str(input_path),
                "status": (
                    str(margin_payload["status"])
                    if isinstance(margin_payload.get("status"), str)
                    else None
                ),
                "contract": str(source_contract) if isinstance(source_contract, str) else None,
                "route_decision": str(source_route) if isinstance(source_route, str) else None,
                "inputs": source_inputs,
                "provenance": source_provenance,
            }
        },
        "inputs": {
            "margin_json": str(input_path),
            "f123_json": source_f123_json,
        },
        "delta1": delta1,
        "delta1_source": margin_payload.get("delta1_source"),
        "source_mu": margin_payload.get("mu"),
        "mu_cancellation": float(delta1) if delta1 is not None and delta1 > 0.0 else None,
        "threshold": 0.0,
        "margin_positive": delta1 is not None and delta1 > 0.0,
        "commutator_measurement_available": bool(measurement_available),
        "commutator_comparison_measured": bool(comparison_measured),
        "commutator_comparison_proxy_unavailable": bool(comparison_proxy_unavailable),
        "clay_promotion": False,
        "collapse_impossible": False,
        "h_delta1_promoting": False,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "theorem_promoted": False,
        "clay_promoted": False,
        "proof_blocking": False,
        "f123_damping_sum_signed": f123_signed,
        "f123_damping_sum_abs": f123_abs,
        "warnings": sorted(set(warnings)),
        "errors": sorted(set(errors)),
        "O": "Upgrade corrected Gronwall margin artifacts into Theorem-G cancellation-margin form.",
        "R": "Load corrected margin output, enforce delta1>0, and set mu_cancellation = delta1.",
        "C": SCRIPT_NAME,
        "S": "Fail-closed, preserving source authority, warnings, and damping metadata.",
        "L": "Malformed input, non-finite/non-positive delta1, or any true promotion flag is an error.",
        "P": ROUTE_DECISION,
        "G": "No theorem, Clay, or promotion claim is introduced by this diagnostic.",
        "F": "Empirical evidence only: all Clay/theorem promotion fields remain false.",
        "changed_files": [str(output_path)],
    }
    return payload, 0 if status != ERROR_STATUS else 1


def _build_error_payload(path: Path, output_path: Path, exc: Exception) -> tuple[dict[str, Any], int]:
    return {
        "schema_version": SCHEMA_VERSION,
        "contract": CONTRACT,
        "status": ERROR_STATUS,
        "script": SCRIPT_NAME,
        "route_decision": ROUTE_DECISION,
        "authority": dict(DEFAULT_AUTHORITY),
        "inputs": {"margin_json": str(path)},
        "delta1": None,
        "mu_cancellation": None,
        "threshold": 0.0,
        "margin_positive": False,
        "commutator_measurement_available": False,
        "commutator_comparison_measured": False,
        "commutator_comparison_proxy_unavailable": True,
        "clay_promotion": False,
        "collapse_impossible": False,
        "h_delta1_promoting": False,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "theorem_promoted": False,
        "clay_promoted": False,
        "proof_blocking": False,
        "f123_damping_sum_signed": None,
        "f123_damping_sum_abs": None,
        "warnings": [],
        "errors": [str(exc)],
        "O": "Upgrade corrected Gronwall margin artifacts into Theorem-G cancellation-margin form.",
        "R": "Load corrected margin output, enforce delta1>0, and set mu_cancellation = delta1.",
        "C": SCRIPT_NAME,
        "S": "Fail-closed, preserving source authority, warnings, and damping metadata.",
        "L": "Malformed input, non-finite/non-positive delta1, or any true promotion flag is an error.",
        "P": ROUTE_DECISION,
        "G": "No theorem, Clay, or promotion claim is introduced by this diagnostic.",
        "F": "Empirical evidence only: all Clay/theorem promotion fields remain false.",
        "changed_files": [str(output_path)],
    }, 1


def main() -> int:
    args = _parse_args()
    try:
        payload, code = _build_payload(args.margin_json, args.output_json)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        payload, code = _build_error_payload(args.margin_json, args.output_json, exc)

    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(
        json.dumps(
            payload,
            sort_keys=True,
            indent=2 if args.pretty else None,
            separators=(",", ":") if not args.pretty else None,
            ensure_ascii=False,
        )
        + ("\n" if args.pretty else ""),
        encoding="utf-8",
    )
    return code


if __name__ == "__main__":
    raise SystemExit(main())
