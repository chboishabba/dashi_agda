#!/usr/bin/env python3
"""Validate ns_case_a_geometric_bridge_summary output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/check_ns_case_a_geometric_bridge_summary.py"
CONTRACT = "check_ns_case_a_geometric_bridge_summary"
SOURCE_CONTRACT = "ns_case_a_geometric_bridge_summary"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_CASE_A_GEOMETRIC_BRIDGE_SUMMARY"
OK_STATUS = "ok"
ERROR_STATUS = "error"
CHECK_ROUTE_DECISION = "FAIL_CLOSED_NS_CASE_A_GEOMETRIC_BRIDGE_SUMMARY_CHECK"

DEFAULT_SUMMARY = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "ns_case_a_geometric_bridge_summary_20260621.json"
)
DEFAULT_OUTPUT = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260620/"
    "check_ns_case_a_geometric_bridge_summary_20260621.json"
)

CONTROL_CARD = {
    "O": "Validate the Case A geometric bridge summary schema and consistency.",
    "R": "Verify the shared thresholds, stats surfaces, and co-movement ledger for the bridge summary.",
    "C": SCRIPT_NAME,
    "S": "Fail-closed validation: malformed inputs or inconsistent bridge arithmetic are hard errors.",
    "L": "Load the bridge summary JSON, validate source ledger and numeric consistency, and emit a checker receipt.",
    "P": CHECK_ROUTE_DECISION,
    "G": "No theorem or Clay claims are permitted by this checker.",
    "F": "Only explicit empirical telemetry with stable threshold joins can pass.",
}

CHECK_CARD_KEYS = ("O", "R", "C", "S", "L", "P", "G", "F")
ALLOWED_STATUSES = {OK_STATUS, ERROR_STATUS}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("summary_json", nargs="?", type=Path, help="Path to the bridge summary JSON.")
    parser.add_argument(
        "--summary-json",
        dest="summary_json_kw",
        type=Path,
        help="Alternative named summary path.",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Optional checker receipt output JSON path.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print checker output.")
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
    path.parent.mkdir(parents=True, exist_ok=True)
    text = (
        json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
        if pretty
        else json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)
    ) + "\n"
    path.write_text(text, encoding="utf-8")


def _record_error(errors: list[str], path: str, message: str) -> None:
    errors.append(f"{path}: {message}")


def _coerce_nonempty_str(value: Any) -> str | None:
    if not isinstance(value, str):
        return None
    value = value.strip()
    return value if value else None


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
        parsed = int(value)
        return parsed if parsed >= 0 else None
    return None


def _check_control_card(payload: dict[str, Any], errors: list[str]) -> None:
    for key in CHECK_CARD_KEYS:
        if _coerce_nonempty_str(payload.get(key)) is None:
            _record_error(errors, "control_card", f"{key} must be a non-empty string")


def _check_contract(payload: dict[str, Any], errors: list[str]) -> None:
    if payload.get("contract") != SOURCE_CONTRACT:
        _record_error(errors, "contract", f"must be {SOURCE_CONTRACT!r}")


def _check_route(payload: dict[str, Any], errors: list[str]) -> None:
    if payload.get("route_decision") != SOURCE_ROUTE_DECISION:
        _record_error(errors, "route_decision", f"must be {SOURCE_ROUTE_DECISION!r}")


def _check_status(payload: dict[str, Any], errors: list[str]) -> None:
    if payload.get("status") not in ALLOWED_STATUSES:
        _record_error(errors, "status", f"must be one of {sorted(ALLOWED_STATUSES)!r}")


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
    for key, expected_value in expected.items():
        value = _coerce_bool(authority.get(key))
        if value is None:
            _record_error(errors, f"authority.{key}", "must be bool")
            continue
        if value is not expected_value:
            _record_error(errors, f"authority.{key}", f"must be {expected_value!r}")


def _check_status_by_source(payload: dict[str, Any], errors: list[str], warnings: list[str]) -> None:
    status_by_source = payload.get("status_by_source")
    if not isinstance(status_by_source, dict):
        _record_error(errors, "status_by_source", "must be a dict")
        return
    for source_name in ("case_a_transition_shell", "boundary_delta1_uniformity"):
        entry = status_by_source.get(source_name)
        if not isinstance(entry, dict):
            _record_error(errors, f"status_by_source.{source_name}", "must be a dict")
            continue
        if _coerce_bool(entry.get("present")) is not True:
            _record_error(errors, f"status_by_source.{source_name}.present", "must be true")
        if entry.get("status") not in {OK_STATUS, ERROR_STATUS}:
            _record_error(errors, f"status_by_source.{source_name}.status", "must be ok|error")
        if _coerce_nonempty_str(entry.get("path")) is None:
            warnings.append(f"status_by_source.{source_name}.path should be a non-empty string")
        if _coerce_nonnegative_int(entry.get("threshold_count")) is None:
            _record_error(errors, f"status_by_source.{source_name}.threshold_count", "must be nonnegative int")


def _check_stats_dict(path: str, stats: Any, errors: list[str], warnings: list[str]) -> None:
    if not isinstance(stats, dict):
        _record_error(errors, path, "must be a dict")
        return
    if _coerce_nonnegative_int(stats.get("count")) is None:
        _record_error(errors, f"{path}.count", "must be nonnegative int")
    for key in ("min", "max", "mean"):
        value = stats.get(key)
        if value is not None and _coerce_finite_float(value) is None:
            warnings.append(f"{path}.{key} should be finite float or null")
    min_value = _coerce_finite_float(stats.get("min"))
    max_value = _coerce_finite_float(stats.get("max"))
    if min_value is not None and max_value is not None and min_value > max_value:
        _record_error(errors, path, "min must not exceed max")


def _check_quantiles(path: str, quantiles: Any, errors: list[str], warnings: list[str]) -> None:
    if not isinstance(quantiles, dict):
        _record_error(errors, path, "must be a dict")
        return
    for key in ("p05", "p25", "p50", "p75", "p95"):
        value = quantiles.get(key)
        if value is not None and _coerce_finite_float(value) is None:
            warnings.append(f"{path}.{key} should be finite float or null")


def _check_bridge_rows(payload: dict[str, Any], errors: list[str], warnings: list[str]) -> list[float]:
    rows = payload.get("bridge_rows")
    if not isinstance(rows, list):
        _record_error(errors, "bridge_rows", "must be a list")
        return []

    thresholds: list[float] = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            _record_error(errors, f"bridge_rows[{index}]", "must be a dict")
            continue
        threshold = _coerce_finite_float(row.get("delta1_threshold"))
        if threshold is None or threshold < 0.0:
            _record_error(errors, f"bridge_rows[{index}].delta1_threshold", "must be finite nonnegative float")
            continue
        thresholds.append(round(threshold, 12))
        case_a = row.get("case_a")
        boundary = row.get("boundary_delta1")
        co_movement = row.get("co_movement")
        if not isinstance(case_a, dict):
            _record_error(errors, f"bridge_rows[{index}].case_a", "must be a dict")
        else:
            for key in ("shell_volume_shrinkage", "boundary_gap_separation", "delta1_min"):
                value = case_a.get(key)
                if value is not None and _coerce_finite_float(value) is None:
                    warnings.append(f"bridge_rows[{index}].case_a.{key} should be finite float or null")
        if not isinstance(boundary, dict):
            _record_error(errors, f"bridge_rows[{index}].boundary_delta1", "must be a dict")
        else:
            for key in ("boundary_gap_separation", "delta1_min"):
                value = boundary.get(key)
                if value is not None and _coerce_finite_float(value) is None:
                    warnings.append(f"bridge_rows[{index}].boundary_delta1.{key} should be finite float or null")
            _check_quantiles(f"bridge_rows[{index}].boundary_delta1.delta1_quantiles", boundary.get("delta1_quantiles"), errors, warnings)
        if not isinstance(co_movement, dict):
            _record_error(errors, f"bridge_rows[{index}].co_movement", "must be a dict")
        else:
            if co_movement.get("same_direction") is not None and not isinstance(co_movement.get("same_direction"), bool):
                warnings.append(f"bridge_rows[{index}].co_movement.same_direction should be bool or null")
    if len(thresholds) != len(set(thresholds)):
        _record_error(errors, "bridge_rows", "duplicate delta1_threshold values")
    return thresholds


def _check_bridge_surface(payload: dict[str, Any], thresholds: list[float], errors: list[str], warnings: list[str]) -> None:
    surface = payload.get("bridge_surface")
    if not isinstance(surface, dict):
        _record_error(errors, "bridge_surface", "must be a dict")
        return

    threshold_count = _coerce_nonnegative_int(surface.get("threshold_count"))
    if threshold_count is None:
        _record_error(errors, "bridge_surface.threshold_count", "must be nonnegative int")
    elif threshold_count != len(thresholds):
        _record_error(errors, "bridge_surface.threshold_count", f"must equal bridge_rows count {len(thresholds)}")

    shared_threshold_count = _coerce_nonnegative_int(surface.get("shared_threshold_count"))
    if shared_threshold_count is None:
        _record_error(errors, "bridge_surface.shared_threshold_count", "must be nonnegative int")
    elif shared_threshold_count != len(set(thresholds)):
        _record_error(
            errors,
            "bridge_surface.shared_threshold_count",
            f"must equal unique bridge threshold count {len(set(thresholds))}",
        )
    shared_thresholds = surface.get("shared_thresholds")
    if not isinstance(shared_thresholds, list):
        _record_error(errors, "bridge_surface.shared_thresholds", "must be a list")
    else:
        if len(shared_thresholds) != len(set(thresholds)):
            _record_error(
                errors,
                "bridge_surface.shared_thresholds",
                f"must contain {len(set(thresholds))} shared thresholds",
            )
        for index, value in enumerate(shared_thresholds):
            if _coerce_finite_float(value) is None:
                warnings.append(f"bridge_surface.shared_thresholds[{index}] should be finite float")

    for key in (
        "shell_volume_shrinkage_stats",
        "boundary_gap_separation_stats",
        "boundary_delta1_min_stats",
    ):
        _check_stats_dict(f"bridge_surface.{key}", surface.get(key), errors, warnings)
    _check_quantiles("bridge_surface.boundary_delta1_quantiles", surface.get("boundary_delta1_quantiles"), errors, warnings)

    co_movement = surface.get("co_movement")
    if not isinstance(co_movement, dict):
        _record_error(errors, "bridge_surface.co_movement", "must be a dict")
    else:
        for key in ("counted_pairs", "same_direction_count", "opposite_direction_count"):
            if _coerce_nonnegative_int(co_movement.get(key)) is None:
                _record_error(errors, f"bridge_surface.co_movement.{key}", "must be nonnegative int")
        for key in ("shell_vs_gap_correlation", "shell_vs_delta1_correlation", "gap_vs_delta1_correlation"):
            value = co_movement.get(key)
            if value is not None and _coerce_finite_float(value) is None:
                warnings.append(f"bridge_surface.co_movement.{key} should be finite float or null")

    monotonicity = surface.get("monotonicity")
    if not isinstance(monotonicity, dict):
        _record_error(errors, "bridge_surface.monotonicity", "must be a dict")
    else:
        for key in ("shell_volume_shrinkage", "boundary_gap_separation", "boundary_delta1_min"):
            value = monotonicity.get(key)
            if value is not None and not isinstance(value, str):
                warnings.append(f"bridge_surface.monotonicity.{key} should be string or null")

    deltas = surface.get("threshold_deltas")
    if not isinstance(deltas, dict):
        _record_error(errors, "bridge_surface.threshold_deltas", "must be a dict")
    else:
        for key in ("shell_volume_shrinkage", "boundary_gap_separation", "boundary_delta1_min"):
            value = deltas.get(key)
            if not isinstance(value, list):
                _record_error(errors, f"bridge_surface.threshold_deltas.{key}", "must be a list")
                continue
            for index, item in enumerate(value):
                if _coerce_finite_float(item) is None:
                    warnings.append(f"bridge_surface.threshold_deltas.{key}[{index}] should be finite float")

    if payload.get("status") == OK_STATUS and not thresholds:
        _record_error(errors, "status", "ok requires at least one shared threshold")


def _check_summary(payload: dict[str, Any]) -> tuple[list[str], list[str]]:
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
    _check_status_by_source(payload, errors, warnings)

    if not isinstance(payload.get("inputs"), dict):
        _record_error(errors, "inputs", "must be a dict")
    row_thresholds = _check_bridge_rows(payload, errors, warnings)
    _check_bridge_surface(payload, row_thresholds, errors, warnings)

    case_a_surface = payload.get("case_a_surface")
    if not isinstance(case_a_surface, dict):
        _record_error(errors, "case_a_surface", "must be a dict")
    else:
        _check_stats_dict("case_a_surface.shell_volume_shrinkage_stats", case_a_surface.get("shell_volume_shrinkage_stats"), errors, warnings)
        _check_stats_dict("case_a_surface.boundary_gap_separation_stats", case_a_surface.get("boundary_gap_separation_stats"), errors, warnings)
        _check_stats_dict("case_a_surface.delta1_min_stats", case_a_surface.get("delta1_min_stats"), errors, warnings)

    boundary_surface = payload.get("boundary_delta1_surface")
    if not isinstance(boundary_surface, dict):
        _record_error(errors, "boundary_delta1_surface", "must be a dict")
    else:
        _check_stats_dict("boundary_delta1_surface.delta1_min_stats", boundary_surface.get("delta1_min_stats"), errors, warnings)
        _check_quantiles("boundary_delta1_surface.delta1_quantiles", boundary_surface.get("delta1_quantiles"), errors, warnings)

    return sorted(set(errors)), sorted(set(warnings))


def main() -> int:
    try:
        args = _parse_args()
        summary_path = _coerce_input_path(args)
    except (OSError, ValueError) as exc:
        result = {
            "contract": CONTRACT,
            "status": ERROR_STATUS,
            "errors": [str(exc)],
            "warnings": [],
            "inputs": {"summary_json": None, "output_json": None},
            "changed_files": [],
            **CONTROL_CARD,
        }
        print(json.dumps(result, sort_keys=True, indent=2))
        return 1

    inputs = {
        "summary_json": str(summary_path),
        "output_json": str(args.output_json),
    }
    changed_files = [str(summary_path)]
    if args.output_json is not None:
        changed_files.append(str(args.output_json))

    payload: dict[str, Any] | None = None
    try:
        payload = _load_json(summary_path)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
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
        "summary_preview": {
            "status": payload.get("status") if isinstance(payload, dict) else None,
            "contract": payload.get("contract") if isinstance(payload, dict) else None,
            "route_decision": payload.get("route_decision") if isinstance(payload, dict) else None,
            "bridge_rows_count": len(payload.get("bridge_rows", [])) if isinstance(payload, dict) else 0,
        },
        **CONTROL_CARD,
    }

    if args.output_json is not None:
        _write_json(args.output_json, result, args.pretty)
    print(json.dumps(result, sort_keys=True, indent=2 if args.pretty else None))
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
