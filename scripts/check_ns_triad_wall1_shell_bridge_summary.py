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
        signed_wall1_rows = payload.get("signed_wall1_rows")
        if signed_wall1_rows is not None and not isinstance(signed_wall1_rows, list):
            errors.append("signed_wall1_rows: must be list or null")
        signed_wall1_status = aggregate.get("signed_wall1_status")
        if signed_wall1_status not in ("fail-closed", "unavailable"):
            errors.append("aggregate.signed_wall1_status: must be 'fail-closed' or 'unavailable'")
        signed_surface_consensus = aggregate.get("signed_surface_consensus")
        if signed_surface_consensus not in ("fail-closed", "unavailable"):
            errors.append("aggregate.signed_surface_consensus: must be 'fail-closed' or 'unavailable'")
        signed_wall1_reconciliation_status = aggregate.get("signed_wall1_reconciliation_status")
        if signed_wall1_reconciliation_status not in ("fail-closed", "unavailable"):
            errors.append(
                "aggregate.signed_wall1_reconciliation_status: must be 'fail-closed' or 'unavailable'"
            )
        signed_wall1_carrier_ranking_status = aggregate.get("signed_wall1_carrier_ranking_status")
        if signed_wall1_carrier_ranking_status not in ("fail-closed", "unavailable"):
            errors.append(
                "aggregate.signed_wall1_carrier_ranking_status: must be 'fail-closed' or 'unavailable'"
            )
        continuous_coherence_capacity_status = aggregate.get("continuous_coherence_capacity_status")
        if continuous_coherence_capacity_status not in ("fail-closed", "unavailable"):
            errors.append(
                "aggregate.continuous_coherence_capacity_status: must be 'fail-closed' or 'unavailable'"
            )
        for key in (
            "continuous_coherence_capacity_candidate_only",
            "continuous_coherence_capacity_fail_closed",
        ):
            value = aggregate.get(key)
            if value is not None and value is not True:
                errors.append(f"aggregate.{key}: must be true or null")
        for prefix in ("amplitude_weighted_negative_frame", "energy_budgeted_fork"):
            if aggregate.get(f"{prefix}_status") not in ("fail-closed", "unavailable"):
                errors.append(f"aggregate.{prefix}_status: must be 'fail-closed' or 'unavailable'")
            if aggregate.get(f"{prefix}_aggregate_status") not in ("fail-closed", "unavailable"):
                errors.append(f"aggregate.{prefix}_aggregate_status: must be 'fail-closed' or 'unavailable'")
            for key in (
                f"{prefix}_candidate_only",
                f"{prefix}_fail_closed",
                f"{prefix}_aggregate_candidate_only",
                f"{prefix}_aggregate_fail_closed",
            ):
                value = aggregate.get(key)
                if value is not None and value is not True:
                    errors.append(f"aggregate.{key}: must be true or null")
            if _nonnegative_int(aggregate.get(f"{prefix}_row_count")) is None:
                errors.append(f"aggregate.{prefix}_row_count: must be nonnegative int or null")
            if _nonnegative_int(aggregate.get(f"{prefix}_surface_count")) is None:
                errors.append(f"aggregate.{prefix}_surface_count: must be nonnegative int or null")
            route_names = aggregate.get(f"{prefix}_route_names")
            if route_names is not None and not isinstance(route_names, list):
                errors.append(f"aggregate.{prefix}_route_names: must be list or null")
        k_n_exact_identity_status = aggregate.get("k_n_exact_identity_status")
        if k_n_exact_identity_status not in ("fail-closed", "unavailable"):
            errors.append("aggregate.k_n_exact_identity_status: must be 'fail-closed' or 'unavailable'")
        for key in (
            "k_n_exact_identity_candidate_only",
            "k_n_exact_identity_fail_closed",
            "k_n_exact_identity_aggregate_status",
            "k_n_exact_identity_aggregate_candidate_only",
            "k_n_exact_identity_aggregate_fail_closed",
        ):
            value = aggregate.get(key)
            if key.endswith("_status"):
                if value not in ("fail-closed", "unavailable"):
                    errors.append(f"aggregate.{key}: must be 'fail-closed' or 'unavailable'")
            elif value is not None and value is not True:
                errors.append(f"aggregate.{key}: must be true or null")
        if signed_wall1_status == "fail-closed" and not signed_wall1_rows:
            errors.append("aggregate.signed_wall1_status: fail-closed requires signed_wall1_rows")
        if signed_wall1_status == "unavailable" and signed_wall1_rows:
            errors.append("aggregate.signed_wall1_status: unavailable requires no signed_wall1_rows")
        if signed_surface_consensus == "fail-closed" and not signed_wall1_rows:
            errors.append("aggregate.signed_surface_consensus: fail-closed requires signed_wall1_rows")
        if signed_surface_consensus == "unavailable" and signed_wall1_rows:
            errors.append("aggregate.signed_surface_consensus: unavailable requires no signed_wall1_rows")
        k_n_exact_identity_rows = payload.get("k_n_exact_identity_rows")
        if k_n_exact_identity_rows is not None and not isinstance(k_n_exact_identity_rows, list):
            errors.append("k_n_exact_identity_rows: must be list or null")
        for key in (
            "signed_wall1_reconciliation_input_status",
            "signed_wall1_carrier_ranking_input_status",
        ):
            if aggregate.get(key) is not None and not isinstance(aggregate.get(key), str):
                errors.append(f"aggregate.{key}: must be string or null")
        if isinstance(signed_wall1_rows, list) and signed_wall1_rows:
            row_count = len(signed_wall1_rows)
            surface_count = len(
                {
                    row.get("surface")
                    for row in signed_wall1_rows
                    if isinstance(row, dict) and isinstance(row.get("surface"), str)
                }
            )
            if _nonnegative_int(aggregate.get("signed_wall1_row_count")) is None:
                errors.append("aggregate.signed_wall1_row_count: must be nonnegative int")
            if _nonnegative_int(aggregate.get("signed_wall1_surface_count")) is None:
                errors.append("aggregate.signed_wall1_surface_count: must be nonnegative int")
            if aggregate.get("signed_wall1_status") != "fail-closed":
                errors.append("aggregate.signed_wall1_status: must be 'fail-closed'")
            if aggregate.get("signed_wall1_candidate_only") is not True:
                errors.append("aggregate.signed_wall1_candidate_only: must be true")
            if aggregate.get("signed_wall1_fail_closed") is not True:
                errors.append("aggregate.signed_wall1_fail_closed: must be true")
            if aggregate.get("signed_wall1_theorem_promoted") is not False:
                errors.append("aggregate.signed_wall1_theorem_promoted: must be false")
            if aggregate.get("signed_wall1_full_ns_promoted") is not False:
                errors.append("aggregate.signed_wall1_full_ns_promoted: must be false")
            if aggregate.get("signed_wall1_clay_promoted") is not False:
                errors.append("aggregate.signed_wall1_clay_promoted: must be false")
            if aggregate.get("signed_xor_bridge_open") is not True:
                errors.append("aggregate.signed_xor_bridge_open: must be true")
            if aggregate.get("signed_spectral_bridge_open") is not True:
                errors.append("aggregate.signed_spectral_bridge_open: must be true")
            if aggregate.get("signed_wall1_reconciliation_status") not in ("fail-closed", "unavailable"):
                errors.append(
                    "aggregate.signed_wall1_reconciliation_status: must be 'fail-closed' or 'unavailable'"
                )
            if aggregate.get("signed_wall1_carrier_ranking_status") not in ("fail-closed", "unavailable"):
                errors.append(
                    "aggregate.signed_wall1_carrier_ranking_status: must be 'fail-closed' or 'unavailable'"
                )
            route_names = aggregate.get("signed_wall1_route_names")
            if route_names is not None and not isinstance(route_names, list):
                errors.append("aggregate.signed_wall1_route_names: must be list or null")
            if route_names not in (
                None,
                ["wall1a-signed-xor-gaugeability", "signed-XY-spectral-frustration-wall-1a"],
            ):
                errors.append(
                    "aggregate.signed_wall1_route_names: must be the ordered signed Wall 1 route list"
                )
            if len(signed_wall1_rows) != 2:
                errors.append("signed_wall1_rows: must contain exactly 2 rows when present")
            if aggregate.get("signed_wall1_row_count") != row_count:
                errors.append("aggregate.signed_wall1_row_count: must match signed_wall1_rows length")
            if aggregate.get("signed_wall1_surface_count") != surface_count:
                errors.append(
                    "aggregate.signed_wall1_surface_count: must match signed_wall1_rows surface count"
                )
            for index, row in enumerate(signed_wall1_rows):
                if not isinstance(row, dict):
                    errors.append(f"signed_wall1_rows[{index}]: must be object")
                    continue
                if row.get("surface") not in (
                    "signed_xor_gaugeability",
                    "signed_spectral_frustration",
                ):
                    errors.append(
                        f"signed_wall1_rows[{index}].surface: must be 'signed_xor_gaugeability' or 'signed_spectral_frustration'"
                    )
                if row.get("candidate_only") is not True:
                    errors.append(f"signed_wall1_rows[{index}].candidate_only: must be true")
                if row.get("fail_closed") is not True:
                    errors.append(f"signed_wall1_rows[{index}].fail_closed: must be true")
                if row.get("theorem_promoted") is not False:
                    errors.append(f"signed_wall1_rows[{index}].theorem_promoted: must be false")
                if row.get("full_ns_promoted") is not False:
                    errors.append(f"signed_wall1_rows[{index}].full_ns_promoted: must be false")
                if row.get("clay_promoted") is not False:
                    errors.append(f"signed_wall1_rows[{index}].clay_promoted: must be false")
                if row.get("wall1_status") != "unproved":
                    errors.append(f"signed_wall1_rows[{index}].wall1_status: must be 'unproved'")
                if row.get("reconciliation_status") not in ("fail-closed", "unavailable"):
                    errors.append(
                        f"signed_wall1_rows[{index}].reconciliation_status: must be 'fail-closed' or 'unavailable'"
                    )
                if row.get("carrier_ranking_status") not in ("fail-closed", "unavailable"):
                    errors.append(
                        f"signed_wall1_rows[{index}].carrier_ranking_status: must be 'fail-closed' or 'unavailable'"
                    )
                if row.get("reconciliation_input_status") is not None and not isinstance(
                    row.get("reconciliation_input_status"), str
                ):
                    errors.append(
                        f"signed_wall1_rows[{index}].reconciliation_input_status: must be string or null"
                    )
                if row.get("carrier_ranking_input_status") is not None and not isinstance(
                    row.get("carrier_ranking_input_status"), str
                ):
                    errors.append(
                        f"signed_wall1_rows[{index}].carrier_ranking_input_status: must be string or null"
                    )
                if row.get("surface") == "signed_xor_gaugeability":
                    if row.get("route_name") != "wall1a-signed-xor-gaugeability":
                        errors.append(
                            f"signed_wall1_rows[{index}].route_name: must be 'wall1a-signed-xor-gaugeability'"
                        )
                    if row.get("boundary_summary") != (
                        "Sign balance does not imply frustration; gaugeable signed XOR is satisfiable; the non-gaugeable signed XOR obstruction surface remains empirical."
                    ):
                        errors.append(
                            f"signed_wall1_rows[{index}].boundary_summary: must match the canonical signed XOR note"
                        )
                    if row.get("bridge_summary") != (
                        "The weighted-distance bridge to gaugeability remains open; d_W(b, im B₂) is the quantitative target."
                    ):
                        errors.append(
                            f"signed_wall1_rows[{index}].bridge_summary: must match the canonical signed XOR bridge note"
                        )
                    if row.get("weighted_distance_target_text") != "d_W(b, im B₂)":
                        errors.append(
                            f"signed_wall1_rows[{index}].weighted_distance_target_text: must be 'd_W(b, im B₂)'"
                        )
                    if row.get("gaugeable_signed_xor_satisfiable") is not True:
                        errors.append(
                            f"signed_wall1_rows[{index}].gaugeable_signed_xor_satisfiable: must be true"
                        )
                    if row.get("non_gaugeable_signed_xor_is_actual_obstruction_surface") is not True:
                        errors.append(
                            f"signed_wall1_rows[{index}].non_gaugeable_signed_xor_is_actual_obstruction_surface: must be true"
                        )
                    if row.get("signed_xor_bridge_open") is not True:
                        errors.append(f"signed_wall1_rows[{index}].signed_xor_bridge_open: must be true")
                else:
                    if row.get("route_name") != "signed-XY-spectral-frustration-wall-1a":
                        errors.append(
                            f"signed_wall1_rows[{index}].route_name: must be 'signed-XY-spectral-frustration-wall-1a'"
                        )
                    if row.get("boundary_summary") != (
                        "Signed Laplacian / signed XY floor candidate remains open, upper spectral edge still carries XY-floor risk, theorem/full-NS/Clay promotion stays false, and the old signed route is legacy and non-canonical."
                    ):
                        errors.append(
                            f"signed_wall1_rows[{index}].boundary_summary: must match the canonical signed spectral note"
                        )
                    if row.get("bridge_summary") != (
                        "The discrete signed-XOR distance to the continuous XY floor bridge is still open."
                    ):
                        errors.append(
                            f"signed_wall1_rows[{index}].bridge_summary: must match the canonical signed spectral bridge note"
                        )
                    if row.get("primary_wall1a_candidate") is not True:
                        errors.append(
                            f"signed_wall1_rows[{index}].primary_wall1a_candidate: must be true"
                        )
                    if row.get("upper_spectral_edge_carries_xy_floor_risk") is not True:
                        errors.append(
                            f"signed_wall1_rows[{index}].upper_spectral_edge_carries_xy_floor_risk: must be true"
                        )
                if row.get("signed_xor_distance_bridge_open") is not True:
                    errors.append(
                        f"signed_wall1_rows[{index}].signed_xor_distance_bridge_open: must be true"
                    )
        if isinstance(k_n_exact_identity_rows, list) and k_n_exact_identity_rows:
            row_count = len(k_n_exact_identity_rows)
            surface_count = len(
                {
                    row.get("surface")
                    for row in k_n_exact_identity_rows
                    if isinstance(row, dict) and isinstance(row.get("surface"), str)
                }
            )
            if _nonnegative_int(aggregate.get("k_n_exact_identity_row_count")) is None:
                errors.append("aggregate.k_n_exact_identity_row_count: must be nonnegative int")
            if _nonnegative_int(aggregate.get("k_n_exact_identity_surface_count")) is None:
                errors.append("aggregate.k_n_exact_identity_surface_count: must be nonnegative int")
            if aggregate.get("k_n_exact_identity_status") != "fail-closed":
                errors.append("aggregate.k_n_exact_identity_status: must be 'fail-closed'")
            if aggregate.get("k_n_exact_identity_candidate_only") is not True:
                errors.append("aggregate.k_n_exact_identity_candidate_only: must be true")
            if aggregate.get("k_n_exact_identity_fail_closed") is not True:
                errors.append("aggregate.k_n_exact_identity_fail_closed: must be true")
            if aggregate.get("k_n_exact_identity_aggregate_status") not in ("fail-closed", "unavailable"):
                errors.append(
                    "aggregate.k_n_exact_identity_aggregate_status: must be 'fail-closed' or 'unavailable'"
                )
            for key in (
                "k_n_exact_identity_aggregate_candidate_only",
                "k_n_exact_identity_aggregate_fail_closed",
            ):
                if aggregate.get(key) is not True:
                    errors.append(f"aggregate.{key}: must be true")
            if len(k_n_exact_identity_rows) != 2:
                errors.append("k_n_exact_identity_rows: must contain exactly 2 rows when present")
            if aggregate.get("k_n_exact_identity_row_count") != row_count:
                errors.append("aggregate.k_n_exact_identity_row_count: must match k_n_exact_identity_rows length")
            if aggregate.get("k_n_exact_identity_surface_count") != surface_count:
                errors.append(
                    "aggregate.k_n_exact_identity_surface_count: must match k_n_exact_identity_rows surface count"
                )
            for index, row in enumerate(k_n_exact_identity_rows):
                if not isinstance(row, dict):
                    errors.append(f"k_n_exact_identity_rows[{index}]: must be object")
                    continue
                if row.get("surface") not in (
                    "k_n_exact_identity_carrier",
                    "b_s_frame_equidistribution_boundary",
                ):
                    errors.append(
                        f"k_n_exact_identity_rows[{index}].surface: must be 'k_n_exact_identity_carrier' or 'b_s_frame_equidistribution_boundary'"
                    )
                if row.get("candidate_only") is not True:
                    errors.append(f"k_n_exact_identity_rows[{index}].candidate_only: must be true")
                if row.get("fail_closed") is not True:
                    errors.append(f"k_n_exact_identity_rows[{index}].fail_closed: must be true")
                if row.get("theorem_promoted") is not False:
                    errors.append(f"k_n_exact_identity_rows[{index}].theorem_promoted: must be false")
                if row.get("full_ns_promoted") is not False:
                    errors.append(f"k_n_exact_identity_rows[{index}].full_ns_promoted: must be false")
                if row.get("clay_promoted") is not False:
                    errors.append(f"k_n_exact_identity_rows[{index}].clay_promoted: must be false")
                if row.get("wall1_status") != "unproved":
                    errors.append(f"k_n_exact_identity_rows[{index}].wall1_status: must be 'unproved'")
                if row.get("k_n_exact_identity_route_open") is not True:
                    errors.append(f"k_n_exact_identity_rows[{index}].k_n_exact_identity_route_open: must be true")
                if row.get("continuous_coherence_route_open") is not True:
                    errors.append(
                        f"k_n_exact_identity_rows[{index}].continuous_coherence_route_open: must be true"
                    )
                if row.get("k_n_exact_identity_status") != "fail-closed":
                    errors.append(f"k_n_exact_identity_rows[{index}].k_n_exact_identity_status: must be 'fail-closed'")
                if row.get("continuous_coherence_status") != "fail-closed":
                    errors.append(
                        f"k_n_exact_identity_rows[{index}].continuous_coherence_status: must be 'fail-closed'"
                    )
                if row.get("route_name") != (
                    "k-n-exact-identity-wall-1a"
                    if row.get("surface") == "k_n_exact_identity_carrier"
                    else "b-s-frame-equidistribution-wall-1a"
                ):
                    errors.append(f"k_n_exact_identity_rows[{index}].route_name: must match the canonical route")
                if row.get("surface") == "k_n_exact_identity_carrier":
                    if row.get("boundary_summary") != (
                        "The K_N exact-identity candidate is the positive Wall 1a carrier, while the old signed-XOR route is legacy and non-canonical."
                    ):
                        errors.append(
                            f"k_n_exact_identity_rows[{index}].boundary_summary: must match the canonical K_N note"
                        )
                    if row.get("bridge_summary") != (
                        "This exact-identity surface is candidate-only and fail-closed; it keeps the positive theorem target explicit without claiming an independent certificate."
                    ):
                        errors.append(
                            f"k_n_exact_identity_rows[{index}].bridge_summary: must match the canonical K_N bridge note"
                        )
                else:
                    if row.get("boundary_summary") != (
                        "The Biot-Savart frame-equidistribution target is the single open finite-dimensional theorem candidate; lower spectral edge controls the floor and upper edge controls frame safety."
                    ):
                        errors.append(
                            f"k_n_exact_identity_rows[{index}].boundary_summary: must match the canonical frame-equidistribution note"
                        )
                    if row.get("bridge_summary") != (
                        "This equidistribution surface is candidate-only and fail-closed; it keeps the exact operator theorem target explicit without claiming a proof."
                    ):
                        errors.append(
                            f"k_n_exact_identity_rows[{index}].bridge_summary: must match the canonical frame-equidistribution bridge note"
                        )
        for key in ("amplitude_weighted_negative_frame_rows", "energy_budgeted_fork_rows"):
            rows_value = payload.get(key)
            if rows_value is not None and not isinstance(rows_value, list):
                errors.append(f"{key}: must be list or null")
            if isinstance(rows_value, list) and rows_value:
                row_count_key = f"{key.removesuffix('_rows')}_row_count"
                if aggregate.get(row_count_key) != len(rows_value):
                    errors.append(f"aggregate.{row_count_key}: must match {key} length")
        if signed_wall1_rows == []:
            if aggregate.get("signed_wall1_row_count") != 0:
                errors.append("aggregate.signed_wall1_row_count: must be 0 when no signed_wall1_rows are present")
            if aggregate.get("signed_wall1_surface_count") != 0:
                errors.append("aggregate.signed_wall1_surface_count: must be 0 when no signed_wall1_rows are present")
            for key in (
                "signed_wall1_candidate_only",
                "signed_wall1_fail_closed",
                "signed_wall1_theorem_promoted",
                "signed_wall1_full_ns_promoted",
                "signed_wall1_clay_promoted",
                "signed_xor_bridge_open",
                "signed_spectral_bridge_open",
                "signed_wall1_route_names",
            ):
                if aggregate.get(key) is not None:
                    errors.append(f"aggregate.{key}: must be null when no signed_wall1_rows are present")
            if aggregate.get("signed_wall1_reconciliation_status") not in ("fail-closed", "unavailable"):
                errors.append(
                    "aggregate.signed_wall1_reconciliation_status: must be 'fail-closed' or 'unavailable' when no signed_wall1_rows are present"
                )
            if aggregate.get("signed_wall1_carrier_ranking_status") not in ("fail-closed", "unavailable"):
                errors.append(
                    "aggregate.signed_wall1_carrier_ranking_status: must be 'fail-closed' or 'unavailable' when no signed_wall1_rows are present"
                )

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
