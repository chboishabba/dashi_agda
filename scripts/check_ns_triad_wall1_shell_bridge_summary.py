#!/usr/bin/env python3
"""Validate ns_triad_wall1_shell_bridge_summary output."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

SCRIPT_NAME = "scripts/check_ns_triad_wall1_shell_bridge_summary.py"
CONTRACT = "check_ns_triad_wall1_shell_bridge_summary"
SOURCE_CONTRACT = "ns_triad_wall1_shell_bridge_summary"
SOURCE_SCRIPT_NAME = "scripts/ns_triad_wall1_shell_bridge_summary.py"
SOURCE_ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_WALL1_SHELL_BRIDGE_SUMMARY"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_WALL1_SHELL_BRIDGE_SUMMARY_CHECK"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
ERROR_STATUS = "error"

DEFAULT_SOURCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_wall1_shell_bridge_summary_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "check_ns_triad_wall1_shell_bridge_summary_20260621.json"
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source_json", nargs="?", type=Path)
    parser.add_argument("--source-json", type=Path, dest="source_json_kw")
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _input_path(args: argparse.Namespace) -> Path:
    if args.source_json is not None and args.source_json_kw is not None:
        raise ValueError("provide either positional source_json or --source-json, not both")
    if args.source_json is None and args.source_json_kw is None:
        return DEFAULT_SOURCE_JSON
    return args.source_json if args.source_json is not None else args.source_json_kw


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _load_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError("payload must be object")
    return payload


def _finite_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _nonnegative_int(value: Any) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value if value >= 0 else None
    if isinstance(value, float) and math.isfinite(value) and value.is_integer() and value >= 0.0:
        return int(value)
    return None


def _fraction(value: Any) -> float | None:
    parsed = _finite_float(value)
    if parsed is None or parsed < -1.0e-12 or parsed > 1.0 + 1.0e-12:
        return None
    return parsed


def main() -> int:
    args = _parse_args()
    source_json = _input_path(args)
    payload = _load_json(source_json)
    errors: list[str] = []

    if payload.get("contract") != SOURCE_CONTRACT:
        errors.append(f"contract: must be {SOURCE_CONTRACT!r}")
    if payload.get("route_decision") != SOURCE_ROUTE_DECISION:
        errors.append(f"route_decision: must be {SOURCE_ROUTE_DECISION!r}")
    if payload.get("script_name") != SOURCE_SCRIPT_NAME:
        errors.append(f"script_name: must be {SOURCE_SCRIPT_NAME!r}")
    for key, expected in (
        ("candidate_only", True),
        ("empirical_non_promoting", True),
        ("fail_closed", True),
    ):
        if payload.get(key) is not expected:
            errors.append(f"{key}: must be {expected!r}")

    rows = payload.get("rows")
    if not isinstance(rows, list):
        errors.append("rows: must be list")
        rows = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            errors.append(f"rows[{index}]: must be object")
            continue
        if _nonnegative_int(row.get("frame")) is None:
            errors.append(f"rows[{index}].frame: must be nonnegative int")
        if _nonnegative_int(row.get("shell")) is None:
            errors.append(f"rows[{index}].shell: must be nonnegative int")
        for key in (
            "cycle_lower_bound_normalized_mean",
            "cycle_lower_bound_normalized_max",
            "cycle_lower_bound_normalized_sum",
            "optimized_lambda_gap_proxy",
            "frustration_floor_ratio_vs_raw",
            "mean_cycle_lower_bound",
            "max_cycle_lower_bound",
            "lower_bound_proxy",
            "cycle_defect_proxy",
            "frustration_floor_proxy",
            "cycle_family_support_overlap_mean",
            "cycle_family_support_overlap_max",
            "cycle_family_support_overlap_density",
            "cycle_family_lower_bound_normalized_mean",
            "cycle_family_lower_bound_normalized_max",
            "cycle_family_lower_bound_normalized_sum",
            "cycle_family_lower_bound",
            "cycle_family_lower_bound_max",
            "cycle_family_packing_concentration",
            "cycle_family_obstruction_collapse_score",
            "cycle_family_normalized_support_vs_F_max",
            "cycle_family_lower_bound_support_over_F_max",
            "cycle_family_lower_bound_support_weighted_sum",
            "strongest_lower_bound_support",
            "family_obstruction_packing_support",
            "family_obstruction_packing_overlap",
            "family_obstruction_packing_lower_bound",
            "family_obstruction_packing_ratio",
            "k01_geometry_ratio",
            "k01_ratio_proxy",
            "k01_geometry_signal",
            "k01_geometry_lower_bound",
            "geometry_alignment_proxy",
            "geometry_stability_proxy",
            "directional_gap_proxy",
            "directional_gap_lower_bound",
            "frame_geometry_proxy",
            "projection_proxy",
            "combined_operator_gap_proxy",
            "dangerous_subspace_weight_fraction",
            "k01_operator_norm",
            "schur_directional_gap_proxy",
            "schur_directional_gap_lower_bound",
            "schur_directional_gap_residual",
            "schur_directional_gap_ratio",
        ):
            value = row.get(key)
            if value is not None and (_finite_float(value) is None or float(value) < -1.0e-12):
                errors.append(f"rows[{index}].{key}: must be finite nonnegative or null")
        support_count = row.get("strongest_lower_bound_support_count")
        if support_count is not None and _nonnegative_int(support_count) is None:
            errors.append(f"rows[{index}].strongest_lower_bound_support_count: must be nonnegative int or null")
        support_source = row.get("strongest_lower_bound_source")
        if row.get("strongest_lower_bound_support") is not None and not isinstance(support_source, str):
            errors.append(f"rows[{index}].strongest_lower_bound_source: must be string when support is present")
        for key in (
            "cycle_family_support_overlap_mean",
            "cycle_family_support_overlap_max",
            "cycle_family_support_overlap_density",
            "cycle_family_packing_concentration",
            "cycle_family_obstruction_collapse_score",
            "family_obstruction_packing_support",
            "family_obstruction_packing_overlap",
            "family_obstruction_packing_ratio",
            "k01_geometry_ratio",
            "k01_ratio_proxy",
            "k01_geometry_signal",
            "geometry_alignment_proxy",
            "geometry_stability_proxy",
            "directional_gap_proxy",
        ):
            value = row.get(key)
            if value is not None and _fraction(value) is None:
                errors.append(f"rows[{index}].{key}: must be finite fraction or null")
        for key in ("family_obstruction_packing_lower_bound", "k01_geometry_lower_bound"):
            value = row.get(key)
            if value is not None and (_finite_float(value) is None or float(value) < -1.0e-12):
                errors.append(f"rows[{index}].{key}: must be finite nonnegative or null")

    aggregate = payload.get("aggregate")
    if not isinstance(aggregate, dict):
        errors.append("aggregate: must be object")
    else:
        if _nonnegative_int(aggregate.get("shared_frame_shell_count")) is None:
            errors.append("aggregate.shared_frame_shell_count: must be nonnegative int")
        if aggregate.get("wall1_status") != "unproved":
            errors.append("aggregate.wall1_status: must be 'unproved'")
        for key in (
            "mean_cycle_lower_bound_mean",
            "max_cycle_lower_bound_mean",
            "frustration_floor_ratio_vs_raw_mean",
            "strongest_lower_bound_support_mean",
            "strongest_lower_bound_support_max",
            "family_obstruction_packing_support_mean",
            "family_obstruction_packing_support_max",
            "family_obstruction_packing_overlap_mean",
            "family_obstruction_packing_overlap_max",
            "family_obstruction_packing_lower_bound_mean",
            "family_obstruction_packing_lower_bound_max",
            "family_obstruction_packing_ratio_mean",
            "family_obstruction_packing_ratio_max",
            "k01_geometry_signal_mean",
            "k01_geometry_signal_max",
            "geometry_alignment_proxy_mean",
            "geometry_alignment_proxy_max",
            "geometry_stability_proxy_mean",
            "geometry_stability_proxy_max",
            "directional_gap_proxy_mean",
            "directional_gap_proxy_max",
            "schur_directional_gap_proxy_mean",
            "schur_directional_gap_proxy_max",
            "schur_directional_gap_lower_bound_mean",
            "schur_directional_gap_residual_mean",
            "schur_directional_gap_ratio_mean",
            "schur_directional_gap_ratio_max",
        ):
            value = aggregate.get(key)
            if value is not None and (_finite_float(value) is None or float(value) < -1.0e-12):
                errors.append(f"aggregate.{key}: must be finite nonnegative or null")
        for key in (
            "phase_gap_vs_cycle_bound_correlation",
            "phase_gap_vs_frame_margin_correlation",
            "floor_ratio_vs_frame_margin_correlation",
            "strongest_lower_bound_support_vs_phase_gap_correlation",
            "strongest_lower_bound_support_vs_frame_margin_correlation",
            "family_obstruction_packing_support_vs_phase_gap_correlation",
            "family_obstruction_packing_support_vs_floor_ratio_correlation",
            "family_obstruction_packing_support_vs_cycle_bound_correlation",
            "family_obstruction_packing_support_vs_k01_geometry_signal_correlation",
            "k01_geometry_signal_vs_phase_gap_correlation",
            "k01_geometry_signal_vs_floor_ratio_correlation",
            "k01_geometry_signal_vs_cycle_bound_correlation",
        ):
            if aggregate.get(key) is not None and _finite_float(aggregate.get(key)) is None:
                errors.append(f"aggregate.{key}: must be finite or null")
        if aggregate.get("strongest_lower_bound_source_modes") is not None and not isinstance(
            aggregate.get("strongest_lower_bound_source_modes"), list
        ):
            errors.append("aggregate.strongest_lower_bound_source_modes: must be list or null")
        for key in ("family_obstruction_packing_support_mean", "family_obstruction_packing_support_max", "k01_geometry_signal_mean", "k01_geometry_signal_max"):
            value = aggregate.get(key)
            if value is not None and (_fraction(value) is None):
                errors.append(f"aggregate.{key}: must be finite fraction or null")
        for key in (
            "family_obstruction_packing_overlap_mean",
            "family_obstruction_packing_overlap_max",
            "family_obstruction_packing_ratio_mean",
            "family_obstruction_packing_ratio_max",
            "geometry_alignment_proxy_mean",
            "geometry_alignment_proxy_max",
            "geometry_stability_proxy_mean",
            "geometry_stability_proxy_max",
            "directional_gap_proxy_mean",
            "directional_gap_proxy_max",
        ):
            value = aggregate.get(key)
            if value is not None and (_fraction(value) is None):
                errors.append(f"aggregate.{key}: must be finite fraction or null")
        schur_status = aggregate.get("schur_directional_audit_status")
        if schur_status is not None and schur_status not in ("fail-closed", "unavailable"):
            errors.append("aggregate.schur_directional_audit_status: must be 'fail-closed' or 'unavailable'")

    status = OK_STATUS if not errors else ERROR_STATUS
    receipt = {
        "contract": CONTRACT,
        "schema_version": SCHEMA_VERSION,
        "route_decision": ROUTE_DECISION,
        "script_name": SCRIPT_NAME,
        "source_json": str(source_json),
        "status": status,
        "ok": status == OK_STATUS,
        "error_count": int(len(errors)),
        "errors": errors,
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(receipt, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(receipt, args.pretty))
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
