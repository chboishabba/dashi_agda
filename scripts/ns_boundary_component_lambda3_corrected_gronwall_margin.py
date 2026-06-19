#!/usr/bin/env python3
"""Corrected Theorem-G margin summary from lambda3/F123 boundary diagnostics.

This script reads lambda3 and optional F123 diagnostic JSON artifacts, computes
``delta1`` and the corrected boundary Gronwall margin ``mu = 2*delta1 - 1/delta1``,
and emits a deterministic summary with non-promoting authority metadata.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_boundary_component_lambda3_corrected_gronwall_margin.py"
CONTRACT = "ns_boundary_component_lambda3_corrected_gronwall_margin"
EXPECTED_LAMBDA3_CONTRACT = "ns_boundary_component_lambda3_diagnostic"
EXPECTED_F123_CONTRACT = "ns_boundary_f123_absorption_diagnostic"
ROUTE_DECISION = "FAIL_CLOSED_NS_BOUNDARY_CORRECTED_GRONWALL_MARGIN"

OK_STATUS = "ok"
WARNING_STATUS = "warning"
ERROR_STATUS = "error"


def _authority() -> dict[str, bool]:
    return {
        "candidate_only": True,
        "empirical_non_promoting": True,
        "truth_authority": False,
        "theorem_authority": False,
        "clay_authority": False,
        "runtime_authority": False,
        "promoted": False,
    }


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2) + "\n"
    return json.dumps(
        payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ) + "\n"


def _coerce_float(value: Any, field: str) -> float:
    if not isinstance(value, (int, float)):
        if isinstance(value, str):
            try:
                value = float(value)
            except ValueError as exc:
                raise ValueError(f"{field} must be numeric, got {value!r}") from exc
        else:
            raise ValueError(f"{field} must be numeric, got {type(value).__name__}")
    if not math.isfinite(float(value)):
        raise ValueError(f"{field} must be finite, got {value!r}")
    return float(value)



def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--lambda3-json",
        type=Path,
        required=True,
        help="Required lambda3 diagnostic JSON (ns_boundary_component_lambda3_diagnostic).",
    )
    parser.add_argument(
        "--f123-json",
        type=Path,
        default=None,
        help="Optional F123 absorption diagnostic JSON (ns_boundary_f123_absorption_diagnostic).",
    )
    parser.add_argument(
        "--delta1",
        type=float,
        default=None,
        help="Optional explicit delta1 override (supersedes lambda3-derived value).",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="Optional output JSON path.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output.")
    return parser.parse_args()


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing input file: {path}")
    with path.open("r", encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"input JSON is not an object: {path}")
    return payload


def _extract_authority(authority: Any) -> tuple[bool, list[str], dict[str, Any]]:
    if not isinstance(authority, dict):
        return False, ["authority_missing_or_not_object"], {}
    required = (
        "candidate_only",
        "empirical_non_promoting",
        "truth_authority",
        "theorem_authority",
        "clay_authority",
        "runtime_authority",
        "promoted",
    )
    for key in required:
        if key not in authority:
            return False, [f"authority_missing:{key}"], {}
    if any(not isinstance(authority.get(key), bool) for key in required):
        return (
            False,
            [
                f"authority_non_bool:{key}"
                for key in required
                if not isinstance(authority.get(key), bool)
            ],
            {},
        )
    return True, [], {key: bool(authority[key]) for key in required}


def _extract_contract(payload: dict[str, Any], expected: str, scope: str, errors: list[str]) -> str | None:
    contract = payload.get("contract")
    if contract is None:
        errors.append(f"{scope}:contract_missing")
        return None
    if not isinstance(contract, str):
        errors.append(f"{scope}:contract_not_string")
        return None
    if contract != expected:
        errors.append(f"{scope}:contract_mismatch_expected_{expected}_got_{contract}")
    return contract


def _extract_status(payload: dict[str, Any], scope: str, errors: list[str]) -> str | None:
    status = payload.get("status")
    if not isinstance(status, str):
        errors.append(f"{scope}:status_missing_or_not_string")
        return None
    return status


def _extract_lambda3_min(payload: dict[str, Any], errors: list[str]) -> tuple[float, str] | tuple[None, str]:
    explicit = payload.get("lambda3_min")
    if explicit is not None:
        try:
            return _coerce_float(explicit, "lambda3_min"), "lambda3_min"
        except ValueError as exc:
            errors.append(str(exc))

    lambda3_stats = payload.get("lambda3_stats")
    if isinstance(lambda3_stats, dict) and "min" in lambda3_stats:
        try:
            return _coerce_float(lambda3_stats["min"], "lambda3_stats.min"), "lambda3_stats.min"
        except ValueError as exc:
            errors.append(str(exc))

    lambda3_min_abs = payload.get("lambda3_min_abs")
    if lambda3_min_abs is not None:
        try:
            return _coerce_float(lambda3_min_abs, "lambda3_min_abs"), "lambda3_min_abs"
        except ValueError as exc:
            errors.append(str(exc))

    errors.append("lambda3_min: no usable numeric field found")
    return None, "missing"


def _positivity_threshold(delta1: float) -> bool:
    return delta1 > 1.0 / math.sqrt(2.0)


def _compute_margin(delta1: float) -> float:
    return 2.0 * delta1 - 1.0 / delta1


def _extract_f123_measurement(
    payload: dict[str, Any],
    f123_path: Path,
    errors: list[str],
) -> tuple[float | None, float | None, bool, list[str]]:
    warnings: list[str] = []
    signed = None
    absolute = None

    damping_signed = payload.get("damping_sum_signed")
    if damping_signed is not None:
        try:
            signed = _coerce_float(damping_signed, "damping_sum_signed")
        except ValueError as exc:
            errors.append(f"{f123_path}: {exc}")

    damping_abs = payload.get("damping_sum_abs")
    if damping_abs is not None:
        try:
            absolute = _coerce_float(damping_abs, "damping_sum_abs")
        except ValueError as exc:
            errors.append(f"{f123_path}: {exc}")

    # Positive commutator measurement is considered available when at least one proxy
    # comparison entry exists and has positive cell support, or when dominance
    # bookkeeping reports proxy availability.
    dominance = payload.get("dominance")
    if isinstance(dominance, dict):
        proxy_available = dominance.get("proxy_available")
        if isinstance(proxy_available, bool):
            if not proxy_available:
                warnings.append("no_positive_commutator_measurement")
            return signed, absolute, bool(proxy_available), warnings

    proxy_comparisons = payload.get("proxy_comparisons")
    if isinstance(proxy_comparisons, list) and proxy_comparisons:
        any_positive = False
        for item in proxy_comparisons:
            if not isinstance(item, dict):
                continue
            if item.get("status") != "ok":
                continue
            dom = item.get("dominance_flags", {})
            if isinstance(dom, dict) and bool(dom.get("pointwise_comparison_available")):
                any_positive = True
                break
        if not any_positive:
            warnings.append("no_positive_commutator_measurement")
        return signed, absolute, any_positive, warnings

    proxy_fields = payload.get("proxy_fields_requested")
    if not proxy_fields:
        warnings.append("no_positive_commutator_measurement")
        return signed, absolute, False, warnings

    warnings.append("no_positive_commutator_measurement")
    return signed, absolute, False, warnings


def _build_payload(
    lambda3_path: Path,
    f123_path: Path | None,
    delta1_override: float | None,
) -> dict[str, Any]:

    errors: list[str] = []
    warnings: list[str] = []

    lambda3_payload = _read_json(lambda3_path)
    lambda3_contract = _extract_contract(
        lambda3_payload, EXPECTED_LAMBDA3_CONTRACT, "lambda3", errors
    )
    lambda3_status = _extract_status(lambda3_payload, "lambda3", errors)

    lambda3_authority = lambda3_payload.get("authority")
    authority_ok, authority_warnings, _ = _extract_authority(lambda3_authority)
    warnings.extend(authority_warnings)
    if not authority_ok:
        errors.extend([f"lambda3:{msg}" for msg in authority_warnings])

    lambda3_min, lambda3_min_source = _extract_lambda3_min(lambda3_payload, errors)
    if lambda3_status != OK_STATUS:
        errors.append("lambda3:status_is_not_ok")

    if delta1_override is not None:
        try:
            delta1 = _coerce_float(delta1_override, "delta1")
            delta1_source = "cli"
        except ValueError as exc:
            errors.append(str(exc))
            delta1 = None
            delta1_source = "invalid"
    else:
        delta1 = lambda3_min
        delta1_source = f"lambda3:{lambda3_min_source}"

    f123_damping_sum_signed: float | None = None
    f123_damping_sum_abs: float | None = None
    positive_commutator_measurement = False
    f123_contract = None
    f123_status = None

    if f123_path is None:
        warnings.append("no_positive_commutator_measurement")
        warnings.append("f123_json_not_provided")
    else:
        f123_payload = _read_json(f123_path)
        f123_contract = _extract_contract(
            f123_payload, EXPECTED_F123_CONTRACT, "f123", errors
        )
        f123_status = _extract_status(f123_payload, "f123", errors)
        if f123_payload.get("authority") is not None:
            fa_ok, fa_warnings, _ = _extract_authority(f123_payload.get("authority"))
            warnings.extend([f"f123:{w}" for w in fa_warnings])
            if not fa_ok:
                errors.append("f123:authority_invalid")
        if f123_status == OK_STATUS:
            (
                f123_damping_sum_signed,
                f123_damping_sum_abs,
                positive_commutator_measurement,
                f123_measurement_warnings,
            ) = _extract_f123_measurement(f123_payload, f123_path, errors)
            warnings.extend(f123_measurement_warnings)
        else:
            warnings.append("f123_status_not_ok")
            warnings.append("no_positive_commutator_measurement")
            warnings.append(f"f123_status:{f123_status!r}")

    if delta1 is None:
        errors.append("delta1_missing")
        status = ERROR_STATUS
    else:
        if not math.isfinite(delta1):
            errors.append("delta1_non_finite")
        if delta1 <= 0.0:
            errors.append("delta1_non_positive")
        if not _positivity_threshold(delta1):
            warnings.append(f"delta1_below_threshold: {delta1:.17g} <= 1/sqrt(2)")

    if errors:
        status = ERROR_STATUS
        margin_positive = False
        mu = None
    else:
        mu = _compute_margin(delta1)
        margin_positive = _positivity_threshold(delta1) and (mu > 0.0)
        status = OK_STATUS if not warnings else WARNING_STATUS

    if f123_path is not None:
        f123_present = True
        f123_path_text = str(f123_path)
    else:
        f123_present = False
        f123_path_text = None

    payload: dict[str, Any] = {
        "schema_version": "1.0.0",
        "contract": CONTRACT,
        "status": status,
        "script": SCRIPT_NAME,
        "route_decision": ROUTE_DECISION,
        "authority": _authority(),
        "provenance": {
            "lambda3": {
                "path": str(lambda3_path),
                "status": lambda3_status,
                "contract": lambda3_contract,
            },
            "f123": {
                "path": f123_path_text,
                "status": f123_status,
                "contract": f123_contract,
                "present": f123_present,
            },
            "delta1_source": delta1_source,
        },
        "inputs": {
            "lambda3_json": str(lambda3_path),
            "f123_json": None if f123_path is None else str(f123_path),
        },
        "lambda3_status": lambda3_status,
        "lambda3_contract": lambda3_contract,
        "lambda3_min": lambda3_min,
        "delta1_source": delta1_source,
        "delta1": delta1,
        "mu": mu,
        "margin_positive": margin_positive,
        "threshold": 1.0 / math.sqrt(2.0),
        "commutator_measurement_available": positive_commutator_measurement,
        "lambda3_distribution_empirical": True,
        "lambda3_distribution_promoting": False,
        "h_delta1_hypothesis": True,
        "h_delta1_promoting": False,
        "f123_absorption_support_only": f123_present and not errors,
        "commutator_comparison_measured": bool(positive_commutator_measurement),
        "commutator_comparison_proxy_unavailable": not positive_commutator_measurement,
        "korn_level_set": False,
        "collapse_impossible": False,
        "clay_promotion": False,
        "f123_damping_sum_signed": f123_damping_sum_signed,
        "f123_damping_sum_abs": f123_damping_sum_abs,
        "warnings": sorted(set(warnings)),
        "errors": sorted(set(errors)),
        "O": "Emit deterministic corrected Theorem-G Gronwall margin evidence from boundary diagnostics.",
        "R": "Load lambda3 and optional f123 outputs, compute delta1 and corrected mu. "
        "Verify commutator measurement availability.",
        "C": SCRIPT_NAME,
        "S": "Validate input JSON schemas and compute a deterministic summary with fail-closed checks.",
        "L": "ok status requires valid required fields; warnings do not block fail-closed completion.",
        "P": ROUTE_DECISION,
        "G": "No theorem, Clay, or promotion route claim is made from this diagnostic.",
        "F": "This artifact is empirical support only; analytic closure and promotions remain false.",
    }

    if warnings and status == OK_STATUS:
        payload["status"] = WARNING_STATUS

    return payload


def main() -> int:
    args = _parse_args()
    try:
        payload = _build_payload(
            lambda3_path=args.lambda3_json,
            f123_path=args.f123_json,
            delta1_override=args.delta1,
        )
    except (FileNotFoundError, ValueError, json.JSONDecodeError) as exc:
        payload = {
            "schema_version": "1.0.0",
            "contract": CONTRACT,
            "status": ERROR_STATUS,
            "script": SCRIPT_NAME,
            "route_decision": ROUTE_DECISION,
            "authority": _authority(),
            "inputs": {
                "lambda3_json": str(args.lambda3_json),
                "f123_json": None if args.f123_json is None else str(args.f123_json),
            },
            "errors": [str(exc)],
            "warnings": [],
            "O": "Emit deterministic corrected Theorem-G Gronwall margin evidence from boundary diagnostics.",
            "R": "Load lambda3 and optional f123 outputs, compute delta1 and corrected mu. "
            "Verify commutator measurement availability.",
            "C": SCRIPT_NAME,
            "S": "Validate input JSON schemas and compute a deterministic summary with fail-closed checks.",
            "L": "missing or invalid fields fail this run.",
            "P": ROUTE_DECISION,
            "G": "No theorem, Clay, or promotion route claim is made from this diagnostic.",
            "F": "This artifact is empirical support only; analytic closure and promotions remain false.",
        }
        if args.output is not None:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(_json_text(payload, args.pretty), encoding="utf-8")
        print(_json_text(payload, args.pretty), end="")
        return 1

    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(_json_text(payload, args.pretty), encoding="utf-8")

    print(_json_text(payload, args.pretty), end="")
    return 1 if payload["status"] == ERROR_STATUS else 0


if __name__ == "__main__":
    raise SystemExit(main())
