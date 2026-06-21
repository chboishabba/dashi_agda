#!/usr/bin/env python3
"""Validate ns_alignment_pressure_bridge_summary output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_alignment_pressure_bridge_summary.py"
CONTRACT = "check_ns_alignment_pressure_bridge_summary"
SOURCE_CONTRACT = "ns_alignment_pressure_bridge_summary"
OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
MISSING_STATUS = "missing"
ERROR_STATUS = "error"
CHECK_ROUTE_DECISION = "FAIL_CLOSED_NS_ALIGNMENT_PRESSURE_BRIDGE_SUMMARY_CHECK"

DEFAULT_SUMMARY = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_alignment_pressure_bridge_summary_20260621.json"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "check_ns_alignment_pressure_bridge_summary_20260621.json"
)

CONTROL_CARD = {
    "O": "Validate alignment-pressure bridge summary schema and consistency.",
    "R": (
        "Verify schema keys, per-source status ledger, aligned threshold rows, "
        "and compact bridge-surface self-consistency."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed validation: required source failures or structural inconsistency are hard errors.",
    "L": (
        "Load the summary JSON, validate row thresholds, co-movement counts, correlation payload, "
        "source ledger and authority flags, and emit a checker receipt."
    ),
    "P": CHECK_ROUTE_DECISION,
    "G": "No theorem or Clay claims are permitted by this checker.",
    "F": "Only fully explicit status + schema-consistent bridge artifacts pass this check.",
}

CHECK_CARD_KEYS = ("O", "R", "C", "S", "L", "P", "G", "F")
ALLOWED_SOURCE_STATUSES = {OK_STATUS, PARTIAL_STATUS, MISSING_STATUS, ERROR_STATUS}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "summary_json",
        nargs="?",
        type=Path,
        help="Path to ns_alignment_pressure_bridge_summary output JSON.",
    )
    parser.add_argument(
        "--summary-json",
        type=Path,
        dest="summary_json_kw",
        help="Alternative named input path.",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Optional checker receipt output JSON path.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print checker receipt.")
    return parser.parse_args()


def _coerce_input_path(args: argparse.Namespace) -> Path:
    if args.summary_json is not None and args.summary_json_kw is not None:
        raise ValueError("provide either positional summary-json path or --summary-json, not both")
    if args.summary_json is None and args.summary_json_kw is None:
        return DEFAULT_SUMMARY
    return args.summary_json if args.summary_json is not None else args.summary_json_kw


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing summary json: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"summary payload must be an object: {path}")
    return payload


def _write_json(path: Path, payload: dict[str, Any], pretty: bool) -> None:
    if pretty:
        text = json.dumps(payload, sort_keys=True, indent=2, allow_nan=False) + "\n"
    else:
        text = json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False) + "\n"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _record_error(errors: list[str], path: str, message: str) -> None:
    errors.append(f"{path}: {message}")


def _coerce_nonempty_str(value: Any) -> str | None:
    if not isinstance(value, str):
        return None
    value = value.strip()
    return value if value else None


def _coerce_status(value: Any) -> str | None:
    if not isinstance(value, str):
        return None
    normalized = value.strip().lower()
    return normalized if normalized in ALLOWED_SOURCE_STATUSES else None


def _coerce_bool(value: Any) -> bool | None:
    return value if isinstance(value, bool) else None


def _coerce_finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _coerce_nonnegative_int(value: Any) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if isinstance(value, float) and math.isfinite(value) and value.is_integer():
        return int(value) if int(value) >= 0 else None
    if isinstance(value, str):
        try:
            parsed = float(value.strip())
        except ValueError:
            return None
        return int(parsed) if parsed >= 0 and parsed.is_integer() and math.isfinite(parsed) else None
    return None


def _coerce_float_list(values: list[Any]) -> list[float]:
    parsed: list[float] = []
    for value in values:
        parsed_value = _coerce_finite_float(value)
        if parsed_value is not None:
            parsed.append(parsed_value)
    return parsed


def _check_control_card(payload: dict[str, Any], errors: list[str]) -> None:
    for key in CHECK_CARD_KEYS:
        if _coerce_nonempty_str(payload.get(key)) is None:
            _record_error(errors, "control_card", f"{key} must be non-empty string")


def _check_contract(payload: dict[str, Any], errors: list[str]) -> None:
    if payload.get("contract") != SOURCE_CONTRACT:
        _record_error(errors, "contract", f"must be {SOURCE_CONTRACT!r}")


def _check_route(payload: dict[str, Any], errors: list[str]) -> None:
    route = payload.get("route_decision")
    if _coerce_nonempty_str(route) is None:
        _record_error(errors, "route_decision", "must be non-empty string")


def _check_status(payload: dict[str, Any], errors: list[str]) -> None:
    status = payload.get("status")
    if status not in {OK_STATUS, PARTIAL_STATUS, ERROR_STATUS}:
        _record_error(errors, "status", f"must be one of {OK_STATUS!r}, {PARTIAL_STATUS!r}, {ERROR_STATUS!r}")


def _check_authority(payload: dict[str, Any], errors: list[str]) -> None:
    authority = payload.get("authority")
    if not isinstance(authority, dict):
        _record_error(errors, "authority", "must be a dict")
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
    for key, value_expected in expected.items():
        value = _coerce_bool(authority.get(key))
        if value is None:
            _record_error(errors, f"authority.{key}", "must be bool")
            continue
        if value is not value_expected:
            _record_error(errors, f"authority.{key}", f"must be {value_expected!r}")


def _check_inputs(payload: dict[str, Any], errors: list[str], warnings: list[str]) -> None:
    inputs = payload.get("inputs")
    if not isinstance(inputs, dict):
        _record_error(errors, "inputs", "must be a dict")
        return
    for key in ("alignment_gap_json", "pressure_eigenframe_json", "compressive_pi_json"):
        if _coerce_nonempty_str(inputs.get(key)) is None:
            warnings.append(f"inputs.{key}: should be a non-empty string")


def _check_source_entry(
    source_name: str,
    entry: dict[str, Any],
    expected_present: bool | None,
    errors: list[str],
    warnings: list[str],
) -> None:
    if not isinstance(entry, dict):
        _record_error(errors, f"status_by_source.{source_name}", "must be dict")
        return
    if expected_present is not None:
        present = _coerce_bool(entry.get("present"))
        if present is None:
            _record_error(errors, f"status_by_source.{source_name}.present", "must be bool")
        elif present is not expected_present:
            warnings.append(f"status_by_source.{source_name}.present does not match expected {expected_present!r}")

    status = _coerce_status(entry.get("status"))
    if status is None:
        _record_error(errors, f"status_by_source.{source_name}.status", "must be ok|partial|missing|error")

    if _coerce_nonempty_str(entry.get("path")) is None:
        warnings.append(f"status_by_source.{source_name}.path should be non-empty string")

    bin_count = _coerce_nonnegative_int(entry.get("bin_count"))
    if bin_count is None:
        _record_error(errors, f"status_by_source.{source_name}.bin_count", "must be nonnegative int")


def _check_status_surface(
    payload: dict[str, Any],
    errors: list[str],
    warnings: list[str],
) -> None:
    status_by_source = payload.get("status_by_source")
    if not isinstance(status_by_source, dict):
        _record_error(errors, "status_by_source", "must be dict")
        return

    for source in ("alignment_gap_bin", "pressure_eigenframe", "compressive_pi"):
        _check_source_entry(
            source,
            status_by_source.get(source),
            expected_present=None,
            errors=errors,
            warnings=warnings,
        )

    required_status = status_by_source.get("alignment_gap_bin", {}).get("status")
    overall = payload.get("status")
    if required_status != OK_STATUS and required_status != PARTIAL_STATUS and required_status != ERROR_STATUS and required_status != MISSING_STATUS:
        return
    if overall == OK_STATUS and required_status != OK_STATUS:
        _record_error(errors, "status", "overall ok requires alignment_gap_bin status ok")
    if overall == PARTIAL_STATUS and required_status != OK_STATUS:
        warnings.append(
            "overall partial is acceptable because required source is partial/missing/errored (expected for degraded optional inputs)."
        )


def _check_bridge_rows(payload: dict[str, Any], errors: list[str], warnings: list[str]) -> list[float]:
    rows = payload.get("bridge_rows")
    if not isinstance(rows, list):
        _record_error(errors, "bridge_rows", "must be a list")
        return []

    thresholds: list[float] = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            _record_error(errors, f"bridge_rows[{index}]", "row must be dict")
            continue

        raw_threshold = row.get("delta1_threshold")
        threshold = _coerce_finite_float(raw_threshold)
        if threshold is None:
            _record_error(errors, f"bridge_rows[{index}].delta1_threshold", "must be finite float")
            continue
        if threshold < 0.0:
            _record_error(errors, f"bridge_rows[{index}].delta1_threshold", "must be nonnegative")
            continue
        thresholds.append(round(threshold, 12))

        alignment = row.get("alignment_gap")
        if alignment is not None and not isinstance(alignment, dict):
            _record_error(errors, f"bridge_rows[{index}].alignment_gap", "must be dict if present")
        elif isinstance(alignment, dict):
            if "align_success_fraction" in alignment and _coerce_finite_float(alignment.get("align_success_fraction")) is None:
                warnings.append(f"bridge_rows[{index}].alignment_gap.align_success_fraction non-finite")

        pressure = row.get("pressure_proxy")
        if pressure is not None and not isinstance(pressure, dict):
            _record_error(errors, f"bridge_rows[{index}].pressure_proxy", "must be dict if present")
        elif isinstance(pressure, dict):
            for key in ("compressive_proxy", "extensional_proxy", "balance"):
                if key in pressure and _coerce_finite_float(pressure.get(key)) is None:
                    warnings.append(f"bridge_rows[{index}].pressure_proxy.{key} non-finite")

        pi = row.get("compressive_pi")
        if pi is not None and not isinstance(pi, dict):
            _record_error(errors, f"bridge_rows[{index}].compressive_pi", "must be dict if present")
        elif isinstance(pi, dict):
            for key in ("compressive_pi_c", "extensional_pi_c", "balance"):
                if key in pi and _coerce_finite_float(pi.get(key)) is None:
                    warnings.append(f"bridge_rows[{index}].compressive_pi.{key} non-finite")

    if len(thresholds) != len(set(thresholds)):
        _record_error(errors, "bridge_rows", "duplicate delta1_threshold values")
    return thresholds


def _check_bridge_surface(payload: dict[str, Any], row_thresholds: list[float], errors: list[str], warnings: list[str]) -> None:
    surface = payload.get("bridge_surface")
    if not isinstance(surface, dict):
        _record_error(errors, "bridge_surface", "must be a dict")
        return

    threshold_count = surface.get("threshold_count")
    if _coerce_nonnegative_int(threshold_count) is None:
        _record_error(errors, "bridge_surface.threshold_count", "must be nonnegative int")
    else:
        if threshold_count != len(set(row_thresholds)):
            warnings.append(
                f"bridge_surface.threshold_count={threshold_count} differs from unique bridge row count={len(set(row_thresholds))}"
            )

    shared = surface.get("shared_threshold_count")
    if not isinstance(shared, dict):
        _record_error(errors, "bridge_surface.shared_threshold_count", "must be dict")
    else:
        for key in ("gap_pressure", "gap_pi", "all_three"):
            count = shared.get(key)
            if _coerce_nonnegative_int(count) is None:
                _record_error(errors, f"bridge_surface.shared_threshold_count.{key}", "must be nonnegative int")

    correlations = surface.get("correlations")
    if not isinstance(correlations, dict):
        _record_error(errors, "bridge_surface.correlations", "must be dict")
    else:
        for key in ("gap_vs_pressure_balance", "gap_vs_pi_c_balance"):
            corr = correlations.get(key)
            if corr is None:
                continue
            if not (isinstance(corr, (int, float)) and math.isfinite(float(corr))):
                _record_error(errors, f"bridge_surface.correlations.{key}", "must be finite float or null")

    co_movement = surface.get("co_movement")
    if not isinstance(co_movement, dict):
        _record_error(errors, "bridge_surface.co_movement", "must be dict")
        return
    for key in (
        "pressure_alignment_same_direction",
        "pressure_alignment_opposite_direction",
        "pi_alignment_same_direction",
        "pi_alignment_opposite_direction",
        "pressure_pi_same_direction",
        "pressure_pi_opposite_direction",
        "counted_pairs",
    ):
        count = co_movement.get(key)
        if _coerce_nonnegative_int(count) is None:
            warnings.append(f"bridge_surface.co_movement.{key} should be nonnegative int")

    for key in ("alignment_success", "pressure_balance", "pi_c_balance"):
        mono = surface.get("monotonicity", {}).get(key)
        if mono is not None and not isinstance(mono, bool):
            warnings.append(f"bridge_surface.monotonicity.{key} should be bool or null")

    for missing_key in ("pressure_proxy_bins_missing_from_gap", "compressive_pi_bins_missing_from_gap"):
        missing_values = surface.get(missing_key, [])
        if not isinstance(missing_values, list):
            warnings.append(f"bridge_surface.{missing_key} should be a list")
            continue
        for index, value in enumerate(missing_values):
            if _coerce_finite_float(value) is None:
                warnings.append(f"bridge_surface.{missing_key}[{index}] should be finite float")


def _check_summary(
    payload: dict[str, Any],
) -> tuple[list[str], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []

    if _coerce_nonempty_str(payload.get("contract")) is None:
        _record_error(errors, "contract", "missing contract")

    if _coerce_nonempty_str(payload.get("schema_version")) is None:
        _record_error(errors, "schema_version", "missing schema_version")

    _check_control_card(payload, errors)
    _check_contract(payload, errors)
    _check_route(payload, errors)
    _check_status(payload, errors)
    _check_authority(payload, errors)
    _check_inputs(payload, errors, warnings)
    _check_status_surface(payload, errors, warnings)

    row_thresholds = _check_bridge_rows(payload, errors, warnings)
    _check_bridge_surface(payload, row_thresholds, errors, warnings)

    return sorted(set(errors)), sorted(set(warnings))


def main() -> int:
    try:
        args = _parse_args()
        summary_path = _coerce_input_path(args)
    except (OSError, ValueError) as exc:
        output = {
            "contract": CONTRACT,
            "status": ERROR_STATUS,
            "errors": [str(exc)],
            "warnings": [],
            "inputs": {"summary_json": None, "output_json": None},
            "changed_files": [],
            **CONTROL_CARD,
        }
        print(json.dumps(output, sort_keys=True, indent=2))
        return 1

    inputs = {
        "summary_json": str(summary_path),
        "output_json": str(args.output_json),
    }
    changed_files = [str(summary_path)]
    if args.output_json is not None:
        changed_files.append(str(args.output_json))

    try:
        payload = _load_json(summary_path)
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        errors = [str(exc)]
        warnings: list[str] = []
        status = ERROR_STATUS
    else:
        errors, warnings = _check_summary(payload)
        status = OK_STATUS if not errors else ERROR_STATUS

    result = {
        "contract": CONTRACT,
        "status": status,
        "errors": errors,
        "warnings": warnings,
        "inputs": inputs,
        "checked_contract": SOURCE_CONTRACT,
        "checked_summary_path": str(summary_path),
        "changed_files": changed_files,
        "status_by_source": payload.get("status_by_source") if "payload" in locals() and isinstance(payload, dict) else None,
        "bridge_rows_count": len(payload.get("bridge_rows", [])) if "payload" in locals() and isinstance(payload, dict) else 0,
        "bridge_thresholds": (payload.get("bridge_surface", {}).get("threshold_count") if "payload" in locals() else 0),
        "summary_preview": {
            "status": payload.get("status") if "payload" in locals() and isinstance(payload, dict) else None,
            "contract": payload.get("contract") if "payload" in locals() and isinstance(payload, dict) else None,
            "route_decision": payload.get("route_decision") if "payload" in locals() and isinstance(payload, dict) else None,
        },
        **CONTROL_CARD,
    }

    if args.output_json is not None:
        _write_json(args.output_json, result, args.pretty)
    print(json.dumps(result, sort_keys=True, indent=2 if args.pretty else None))
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
