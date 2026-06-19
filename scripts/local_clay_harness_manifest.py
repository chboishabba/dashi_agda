#!/usr/bin/env python3
"""Fast local Clay diagnostic harness manifest runner.

This integration runner discovers the current local diagnostic harnesses for
the fail-closed NS/YM/unification lanes, executes a deliberately small smoke
subset, and writes a single manifest:

    outputs/local_clay_harness_manifest.json

It is not a proof checker and never promotes Clay/YM/unification claims.
Child harness output files are routed to:

    outputs/local_clay_harness_manifest_children/

The child outputs are intentionally stable local receipts for high-alpha
diagnostics.  This is still a fail-closed diagnostic integration runner, not a
proof checker.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT = REPO_ROOT / "outputs" / "local_clay_harness_manifest.json"
CHILD_OUT_DIR = REPO_ROOT / "outputs" / "local_clay_harness_manifest_children"
DEFAULT_TIMEOUT_SECONDS = 25


@dataclass(frozen=True)
class HarnessSpec:
    name: str
    path: Path
    args: tuple[str, ...] = ()
    expected_json_path: Path | None = None
    optional: bool = False
    skip_reason: str | None = None
    notes: tuple[str, ...] = ()


@dataclass
class HarnessResult:
    name: str
    discovered: bool
    promotion: bool = False
    command: list[str] = field(default_factory=list)
    return_code: int | None = None
    duration_seconds: float | None = None
    parsed_json_summary: Any | None = None
    parsed_json_source: str | None = None
    stdout_tail: str = ""
    stderr_tail: str = ""
    skipped: bool = False
    skip_reason: str | None = None
    notes: list[str] = field(default_factory=list)


def rel(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def tail_text(text: str, limit: int = 4000) -> str:
    if len(text) <= limit:
        return text
    return text[-limit:]


def extract_first_json(text: str) -> Any | None:
    decoder = json.JSONDecoder()
    for index, char in enumerate(text):
        if char not in "[{":
            continue
        try:
            value, _ = decoder.raw_decode(text[index:])
        except json.JSONDecodeError:
            continue
        return value
    return None


def parse_key_value_summary(text: str) -> dict[str, str]:
    summary: dict[str, str] = {}
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped or "=" not in stripped:
            continue
        key, value = stripped.split("=", 1)
        key = key.strip()
        value = value.strip()
        if key and len(key) <= 80:
            summary[key] = value
    return summary


def parse_json_file(path: Path) -> Any | None:
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None


def summarize_json(value: Any, max_rows: int = 8) -> Any:
    """Keep parsed JSON useful but compact enough for an integration receipt."""
    if isinstance(value, dict):
        summarized: dict[str, Any] = {}
        preferred = (
            "contract",
            "scope",
            "status",
            "harness",
            "ok",
            "diagnostic_only",
            "warning",
            "control",
            "promotion",
            "clay_promotion",
            "quick",
            "inputs",
            "parameters",
            "params",
            "counts",
            "summary",
            "aggregate",
            "cases",
            "regimes",
            "metrics",
            "classification",
            "interpretation",
            "skipped",
            "triads_accepted",
            "zero_hits_single_depth",
            "hit_fraction_single_depth",
            "family_i_hits",
            "family_ii_hits",
            "estimated_width_zero_outputs",
            "estimated_width_all_outputs",
            "depth2_continuation_hits",
            "depth2_hit_fraction_among_single_hits",
            "frame_model",
            "frame_source",
            "field_summary",
            "triadic_sampling",
            "depth_stats",
            "depths",
        )
        for key in preferred:
            if key in value:
                summarized[key] = summarize_json(value[key], max_rows=max_rows)
        if not summarized:
            for key, item in list(value.items())[:max_rows]:
                summarized[str(key)] = summarize_json(item, max_rows=max_rows)
        if "rows" in value and isinstance(value["rows"], list):
            summarized["rows_count"] = len(value["rows"])
            summarized["rows_head"] = summarize_json(value["rows"][:max_rows], max_rows=max_rows)
        if "sample_rows" in value and isinstance(value["sample_rows"], list):
            summarized["sample_rows_count"] = len(value["sample_rows"])
            summarized["sample_rows_head"] = summarize_json(
                value["sample_rows"][: min(3, max_rows)], max_rows=max_rows
            )
        return summarized
    if isinstance(value, list):
        return [summarize_json(item, max_rows=max_rows) for item in value[:max_rows]]
    return value


def script(path: str) -> Path:
    return REPO_ROOT / "scripts" / path


def build_specs() -> list[HarnessSpec]:
    CHILD_OUT_DIR.mkdir(parents=True, exist_ok=True)
    py = sys.executable
    ym_bt_out = CHILD_OUT_DIR / "ym_bt_tree_spectral_gap_smoke.json"
    ym_boundary_regression_out = CHILD_OUT_DIR / "ym_bt_boundary_depth_regression_smoke.json"
    ym_boundary_regression_harness_out = CHILD_OUT_DIR / "ym_bt_boundary_depth_regression_base_harness.json"
    dobrushin_out = CHILD_OUT_DIR / "ym_bt_dobrushin_influence_smoke.json"
    ym_selfadjoint_proxy_out = (
        CHILD_OUT_DIR / "ym_finite_selfadjoint_hamiltonian_proxy_smoke.json"
    )
    ym_hamiltonian_domination_proxy_out = (
        CHILD_OUT_DIR / "ym_hamiltonian_domination_proxy_smoke.json"
    )
    ym_domination_spectral_margin_proxy_out = (
        CHILD_OUT_DIR / "ym_domination_spectral_margin_proxy_smoke.json"
    )
    ym_spectral_margin_boundary_sensitivity_out = (
        CHILD_OUT_DIR / "ym_spectral_margin_boundary_sensitivity_smoke.json"
    )
    ym_killing_boundary_self_adjointness_proxy_out = (
        CHILD_OUT_DIR / "ym_killing_boundary_self_adjointness_proxy_smoke.json"
    )
    ym_seiler_continuum_route_out = (
        CHILD_OUT_DIR / "ym_seiler_continuum_route_smoke.json"
    )
    ym_continuum_uniform_rho_bound_out = (
        CHILD_OUT_DIR / "ym_continuum_uniform_rho_bound_smoke.json"
    )
    ym_continuum_uniform_leakage_bound_out = (
        CHILD_OUT_DIR / "ym_continuum_uniform_leakage_bound_smoke.json"
    )
    ym_hyperbolic_shimura_to_euclidean_universality_out = (
        CHILD_OUT_DIR / "ym_hyperbolic_shimura_to_euclidean_universality_smoke.json"
    )
    ym_killing_boundary_theorem_out = (
        CHILD_OUT_DIR / "ym_killing_boundary_theorem_smoke.json"
    )
    ym_opposite_face_involution_theorem_out = (
        CHILD_OUT_DIR / "ym_opposite_face_involution_theorem_smoke.json"
    )
    ym_flux_cancellation_theorem_out = (
        CHILD_OUT_DIR / "ym_flux_cancellation_theorem_smoke.json"
    )
    ym_gauge_quotient_descent_theorem_out = (
        CHILD_OUT_DIR / "ym_gauge_quotient_descent_theorem_smoke.json"
    )
    ym_quotient_symmetry_theorem_out = (
        CHILD_OUT_DIR / "ym_quotient_symmetry_theorem_smoke.json"
    )
    ym_killing_boundary_child_composite_out = (
        CHILD_OUT_DIR / "ym_killing_boundary_child_composite_smoke.json"
    )
    ym_selfadjoint_to_domination_precondition_out = (
        CHILD_OUT_DIR / "ym_selfadjoint_to_domination_precondition_smoke.json"
    )
    ym_domination_spectral_margin_route_out = (
        CHILD_OUT_DIR / "ym_domination_spectral_margin_route_smoke.json"
    )
    ym_continuum_nospectral_route_out = (
        CHILD_OUT_DIR / "ym_continuum_nospectral_route_smoke.json"
    )
    ym_orientation_sign_cancellation_out = (
        CHILD_OUT_DIR / "ym_orientation_sign_cancellation_smoke.json"
    )
    ym_spectral_gap_explicit_constant_out = (
        CHILD_OUT_DIR / "ym_spectral_gap_explicit_constant_smoke.json"
    )
    ym_step_scaling_global_bound_out = (
        CHILD_OUT_DIR / "ym_step_scaling_global_bound_smoke.json"
    )
    ym_reflection_positivity_boundary_convention_out = (
        CHILD_OUT_DIR / "ym_reflection_positivity_boundary_convention_smoke.json"
    )
    ym_os_wightman_massgap_route_out = (
        CHILD_OUT_DIR / "ym_os_wightman_massgap_route_smoke.json"
    )
    ym_reflection_positivity_child_out = (
        CHILD_OUT_DIR / "ym_reflection_positivity_child_smoke.json"
    )
    ym_final_assembly_clay_blocker_out = (
        CHILD_OUT_DIR / "ym_final_assembly_clay_blocker_smoke.json"
    )
    ym_reflection_positivity_consolidation_out = (
        CHILD_OUT_DIR / "ym_reflection_positivity_consolidation_smoke.json"
    )
    ym_final_authority_packaging_out = (
        CHILD_OUT_DIR / "ym_final_authority_packaging_smoke.json"
    )
    ym_reflection_positivity_spatial_tau_theta_commutativity_out = (
        CHILD_OUT_DIR / "ym_reflection_positivity_spatial_tau_theta_commutativity_smoke.json"
    )
    ym_reflection_positivity_action_split_out = (
        CHILD_OUT_DIR / "ym_reflection_positivity_action_split_smoke.json"
    )
    ym_reflection_positivity_transfer_matrix_hermitian_out = (
        CHILD_OUT_DIR / "ym_reflection_positivity_transfer_matrix_hermitian_smoke.json"
    )
    ym_reflection_positivity_os_axiom_out = (
        CHILD_OUT_DIR / "ym_reflection_positivity_os_axiom_smoke.json"
    )
    ym_reflection_positivity_full_theorem_assembly_out = (
        CHILD_OUT_DIR / "ym_reflection_positivity_full_theorem_assembly_smoke.json"
    )
    ym_only_remaining_authority_blockers_out = (
        CHILD_OUT_DIR / "ym_only_remaining_authority_blockers_smoke.json"
    )
    ym_standard_language_writeup_readiness_out = (
        CHILD_OUT_DIR / "ym_standard_language_writeup_readiness_smoke.json"
    )
    ym_standard_language_paper_assembly_out = (
        CHILD_OUT_DIR / "ym_standard_language_paper_assembly_smoke.json"
    )
    ym_paper_submission_packet_out = (
        CHILD_OUT_DIR / "ym_paper_submission_packet_smoke.json"
    )
    ym_killing_boundary_flux_pairing_out = (
        CHILD_OUT_DIR / "ym_killing_boundary_flux_pairing_smoke.json"
    )
    ym_gauge_quotient_domain_out = (
        CHILD_OUT_DIR / "ym_gauge_quotient_domain_smoke.json"
    )
    defect_four_point_out = CHILD_OUT_DIR / "defect_four_point_smoke.json"
    defect_hierarchy_out = CHILD_OUT_DIR / "defect_hierarchy_hypothesis_search_smoke.json"
    gluing_linearity_out = CHILD_OUT_DIR / "gluing_operator_linearity_proxy_smoke.json"
    gluing_quotient_admissibility_out = (
        CHILD_OUT_DIR / "unification_gluing_quotient_admissibility_proxy_smoke.json"
    )
    unification_cross_term_nullity_theorem_out = (
        CHILD_OUT_DIR / "unification_cross_term_nullity_theorem_smoke.json"
    )
    unification_null_class_stability_theorem_out = (
        CHILD_OUT_DIR / "unification_null_class_stability_theorem_smoke.json"
    )
    unification_null_transport_modulo_null_consumer_out = (
        CHILD_OUT_DIR / "unification_null_transport_modulo_null_consumer_smoke.json"
    )
    unification_cross_term_child_composite_out = (
        CHILD_OUT_DIR / "unification_cross_term_child_composite_smoke.json"
    )
    unification_hc_composite_out = (
        CHILD_OUT_DIR / "unification_hc_composite_smoke.json"
    )
    unification_modulo_null_four_point_route_out = (
        CHILD_OUT_DIR / "unification_modulo_null_four_point_route_smoke.json"
    )
    unification_parallelogram_jvn_route_out = (
        CHILD_OUT_DIR / "unification_parallelogram_jvn_route_smoke.json"
    )
    unification_discriminant_cross_term_out = (
        CHILD_OUT_DIR / "unification_discriminant_cross_term_smoke.json"
    )
    unification_null_class_subspace_out = (
        CHILD_OUT_DIR / "unification_null_class_subspace_smoke.json"
    )
    unification_parallelogram_from_bilinear_out = (
        CHILD_OUT_DIR / "unification_parallelogram_from_bilinear_smoke.json"
    )
    unification_u1ah_ns_lane_out = (
        CHILD_OUT_DIR / "unification_u1ah_ns_lane_smoke.json"
    )
    unification_u1ah_ym_lane_out = (
        CHILD_OUT_DIR / "unification_u1ah_ym_lane_smoke.json"
    )
    unification_u1ah_global_lane_out = (
        CHILD_OUT_DIR / "unification_u1ah_global_lane_smoke.json"
    )
    unification_clifford_signature_table_out = (
        CHILD_OUT_DIR / "unification_clifford_signature_table_smoke.json"
    )
    unification_u1ah_per_lane_composite_out = (
        CHILD_OUT_DIR / "unification_u1ah_per_lane_composite_smoke.json"
    )
    unification_signature_clifford_consumer_socket_out = (
        CHILD_OUT_DIR / "unification_signature_clifford_consumer_socket_smoke.json"
    )
    unification_lane_justification_authority_out = (
        CHILD_OUT_DIR / "unification_lane_justification_authority_smoke.json"
    )
    ns_writeup_and_constants_readiness_out = (
        CHILD_OUT_DIR / "ns_writeup_and_constants_readiness_smoke.json"
    )
    ns_standard_pde_writeup_assembly_out = (
        CHILD_OUT_DIR / "ns_standard_pde_writeup_assembly_smoke.json"
    )
    unification_consumer_authority_assembly_out = (
        CHILD_OUT_DIR / "unification_consumer_authority_assembly_smoke.json"
    )
    ns_paper_submission_packet_out = (
        CHILD_OUT_DIR / "ns_paper_submission_packet_smoke.json"
    )
    ns_boundary_component_lambda3_out = (
        CHILD_OUT_DIR / "ns_boundary_component_lambda3_diagnostic_smoke.json"
    )
    ns_boundary_f123_absorption_out = (
        CHILD_OUT_DIR / "ns_boundary_f123_absorption_diagnostic_smoke.json"
    )
    ns_boundary_corrected_gronwall_margin_out = (
        CHILD_OUT_DIR / "ns_boundary_corrected_gronwall_margin_smoke.json"
    )
    ns_boundary_timeseries_margin_summary_out = (
        CHILD_OUT_DIR / "ns_boundary_timeseries_margin_summary_smoke.json"
    )
    ns_boundary_gronwall_margin_regression_out = (
        CHILD_OUT_DIR / "ns_boundary_gronwall_margin_regression_smoke.json"
    )
    ns_boundary_theoremg_cancellation_margin_out = (
        CHILD_OUT_DIR / "ns_boundary_theoremg_cancellation_margin_smoke.json"
    )
    ns_boundary_cancellation_margin_regression_out = (
        CHILD_OUT_DIR / "ns_boundary_cancellation_margin_regression_smoke.json"
    )
    ns_boundary_pressure_poisson_bypass_out = (
        CHILD_OUT_DIR / "ns_boundary_pressure_poisson_bypass_smoke.json"
    )
    ns_boundary_geometric_concentration_out = (
        CHILD_OUT_DIR / "ns_boundary_geometric_concentration_smoke.json"
    )
    ns_boundary_pressure_geometric_regression_out = (
        CHILD_OUT_DIR / "ns_boundary_pressure_geometric_regression_smoke.json"
    )
    ns_boundary_g12_bounds_out = (
        CHILD_OUT_DIR / "ns_boundary_g12_bounds_smoke.json"
    )
    ns_interior_vorticity_budget_out = (
        CHILD_OUT_DIR / "ns_interior_vorticity_budget_smoke.json"
    )
    ns_omega_l3_timeseries_out = (
        CHILD_OUT_DIR / "ns_omega_l3_timeseries_smoke.json"
    )
    ns_layer_l2_vorticity_fraction_out = (
        CHILD_OUT_DIR / "ns_layer_l2_vorticity_fraction_smoke.json"
    )
    ns_layer_l2_vorticity_fraction_summary_out = (
        CHILD_OUT_DIR / "ns_layer_l2_vorticity_fraction_summary_smoke.json"
    )
    ns_layer_l2_vorticity_fraction_regression_out = (
        CHILD_OUT_DIR / "ns_layer_l2_vorticity_fraction_regression_smoke.json"
    )
    ns_pressure_poisson_sign_audit_out = (
        CHILD_OUT_DIR / "ns_pressure_poisson_sign_audit_smoke.json"
    )
    ns_interior_pressure_regression_out = (
        CHILD_OUT_DIR / "ns_interior_pressure_regression_smoke.json"
    )
    ns_pressure_poisson_sign_timeseries_out = (
        CHILD_OUT_DIR / "ns_pressure_poisson_sign_timeseries_smoke.json"
    )
    ns_interior_budget_timeseries_out = (
        CHILD_OUT_DIR / "ns_interior_budget_timeseries_smoke.json"
    )
    ns_pressure_poisson_bypass_convention_normalized_out = (
        CHILD_OUT_DIR / "ns_pressure_poisson_bypass_convention_normalized_smoke.json"
    )
    ns_pressure_convention_regression_out = (
        CHILD_OUT_DIR / "ns_pressure_convention_regression_smoke.json"
    )
    ns_boundary_derived_smoke_candidates = tuple(
        sorted(Path("/tmp").glob("ns_boundary_derived*.npz"))
    )
    ns_boundary_smoke_derived_input = (
        ns_boundary_derived_smoke_candidates[0]
        if ns_boundary_derived_smoke_candidates
        else None
    )
    ns_raw_pressure_smoke_candidates = tuple(
        sorted(Path("/tmp").glob("ns3d*_pressure*.npz"))
    )
    ns_raw_pressure_smoke_input = (
        ns_raw_pressure_smoke_candidates[0]
        if ns_raw_pressure_smoke_candidates
        else None
    )
    unification_authority_review_packet_out = (
        CHILD_OUT_DIR / "unification_authority_review_packet_smoke.json"
    )
    unification_modulo_null_linearity_out = (
        CHILD_OUT_DIR / "unification_modulo_null_linearity_smoke.json"
    )
    unification_scale_invariant_cross_term_out = (
        CHILD_OUT_DIR / "unification_scale_invariant_cross_term_smoke.json"
    )
    ns_propagated_out = CHILD_OUT_DIR / "ns_propagated_polarization_coherence_smoke.json"
    ns_exact_leakage_out = CHILD_OUT_DIR / "ns_exact_leakage_coherence_audit_smoke.json"
    ns_exact_sweep_out = CHILD_OUT_DIR / "ns_exact_strain_threshold_polarization_sweep_smoke.json"
    ns_sign_depth_out = CHILD_OUT_DIR / "ns_sign_antisymmetry_depth_sweep_smoke.json"
    ns_jacobian_out = CHILD_OUT_DIR / "ns_propagated_coherence_jacobian_smoke.json"
    ns_signed_leakage_out = CHILD_OUT_DIR / "ns_signed_leakage_obstruction_smoke.json"
    ns_s2_cascade_width_out = CHILD_OUT_DIR / "ns_s2_cascade_width_smoke.json"
    ns_rank_one_audit_out = CHILD_OUT_DIR / "ns_leray_rank_one_symbol_audit_smoke.json"
    ns_kappa_arcsine_out = CHILD_OUT_DIR / "ns_kappa_arcsine_law_smoke.json"
    ns_stretching_formula_out = CHILD_OUT_DIR / "ns_stretching_formula_smoke.json"
    ns_strain_mean_square_out = CHILD_OUT_DIR / "ns_strain_mean_square_formula_smoke.json"
    ns_kappa_bias_out = CHILD_OUT_DIR / "ns_kappa_bias_variational_smoke.json"
    ns_a4_four_part_proof_out = CHILD_OUT_DIR / "ns_a4_four_part_proof_smoke.json"
    ns_a4_error_budget_threshold_out = (
        CHILD_OUT_DIR / "ns_a4_error_budget_threshold_smoke.json"
    )
    ns_a5_kappa_bias_vanishing_out = (
        CHILD_OUT_DIR / "ns_a5_kappa_bias_vanishing_smoke.json"
    )
    ns_a1_type_i_abel_mass_route_out = (
        CHILD_OUT_DIR / "ns_a1_type_i_abel_mass_route_smoke.json"
    )
    ns_a1_type_i_abel_mass_theorem_out = (
        CHILD_OUT_DIR / "ns_a1_type_i_abel_mass_theorem_smoke.json"
    )
    ns_a2_near_diagonal_coifman_meyer_out = (
        CHILD_OUT_DIR / "ns_a2_near_diagonal_coifman_meyer_smoke.json"
    )
    ns_a2_near_diagonal_coifman_meyer_theorem_out = (
        CHILD_OUT_DIR / "ns_a2_near_diagonal_coifman_meyer_theorem_smoke.json"
    )
    ns_a8_full_local_defect_monotonicity_out = (
        CHILD_OUT_DIR / "ns_a8_full_local_defect_monotonicity_smoke.json"
    )
    ns_a8_annular_decay_clarification_out = (
        CHILD_OUT_DIR / "ns_a8_annular_decay_clarification_smoke.json"
    )
    ns_a8_scale_monotonicity_out = (
        CHILD_OUT_DIR / "ns_a8_scale_monotonicity_smoke.json"
    )
    ns_a6_triadic_compensated_leakage_out = (
        CHILD_OUT_DIR / "ns_a6_triadic_compensated_leakage_smoke.json"
    )
    ns_a7_residual_depletion_gronwall_out = (
        CHILD_OUT_DIR / "ns_a7_residual_depletion_gronwall_smoke.json"
    )
    ns_a9_ckn_bkm_closure_out = (
        CHILD_OUT_DIR / "ns_a9_ckn_bkm_closure_smoke.json"
    )
    ns_a9_singularity_contradiction_route_out = (
        CHILD_OUT_DIR / "ns_a9_singularity_contradiction_route_smoke.json"
    )
    ns_a8_a9_closure_pipeline_out = (
        CHILD_OUT_DIR / "ns_a8_a9_closure_pipeline_smoke.json"
    )
    ns_typei_kappa_bias_out = CHILD_OUT_DIR / "ns_typeI_selfsimilar_kappa_bias_smoke.json"
    ns_abel_triadic_measure_proxy_out = (
        CHILD_OUT_DIR / "ns_abel_triadic_measure_proxy_smoke.json"
    )
    ns_kappa_bias_profile_sweep_out = (
        CHILD_OUT_DIR / "ns_kappa_bias_profile_sweep_smoke.json"
    )
    ns_gaussian_balance_out = CHILD_OUT_DIR / "ns_gaussian_selfsimilar_kappa_bias_balance_smoke.json"
    ns_transfer_operator_bias_out = (
        CHILD_OUT_DIR / "ns_transfer_operator_bias_neutrality_smoke.json"
    )
    ns_abel_triadic_stationarity_proxy_out = (
        CHILD_OUT_DIR / "ns_abel_triadic_stationarity_proxy_smoke.json"
    )
    ns_stationarity_rate_proxy_out = (
        CHILD_OUT_DIR / "ns_stationarity_rate_proxy_smoke.json"
    )
    ns_bounded_abel_mass_proxy_out = (
        CHILD_OUT_DIR / "ns_bounded_abel_mass_proxy_smoke.json"
    )
    ns_biot_savart_shell_localization_proxy_out = (
        CHILD_OUT_DIR / "ns_biot_savart_shell_localization_proxy_smoke.json"
    )
    ns_lrt_fourier_output_coupling_proxy_out = (
        CHILD_OUT_DIR / "ns_lrt_fourier_output_coupling_proxy_smoke.json"
    )
    ns_bony_paraproduct_a6_repair_proxy_out = (
        CHILD_OUT_DIR / "ns_bony_paraproduct_a6_repair_proxy_smoke.json"
    )
    ns_pointwise_to_abel_proxy_out = (
        CHILD_OUT_DIR / "ns_pointwise_to_abel_averaging_proxy_smoke.json"
    )
    ns_localization_pressure_proxy_out = (
        CHILD_OUT_DIR / "ns_localization_pressure_commutator_proxy_smoke.json"
    )
    ns_cutoff_riesz_commutator_kernel_proxy_out = (
        CHILD_OUT_DIR / "ns_cutoff_riesz_commutator_kernel_proxy_smoke.json"
    )
    ns_pressure_tail_absorption_proxy_out = (
        CHILD_OUT_DIR / "ns_pressure_tail_absorption_proxy_smoke.json"
    )
    ns_harmonic_pressure_tail_decay_proxy_out = (
        CHILD_OUT_DIR / "ns_harmonic_pressure_tail_decay_proxy_smoke.json"
    )
    ns_pressure_localization_subbudget_proxy_out = (
        CHILD_OUT_DIR / "ns_pressure_localization_subbudget_proxy_smoke.json"
    )
    ns_pressure_subbudget_component_sensitivity_out = (
        CHILD_OUT_DIR / "ns_pressure_subbudget_component_sensitivity_smoke.json"
    )
    ns_a6_error_budget_proxy_out = (
        CHILD_OUT_DIR / "ns_a6_error_budget_proxy_smoke.json"
    )
    unification_quotient_four_point_stress_out = (
        CHILD_OUT_DIR / "unification_quotient_four_point_stress_smoke.json"
    )
    unification_cross_term_to_four_point_pipeline_out = (
        CHILD_OUT_DIR / "unification_cross_term_to_four_point_pipeline_smoke.json"
    )
    unification_hierarchy_consistency_kills_four_point_defect_out = (
        CHILD_OUT_DIR / "unification_hierarchy_consistency_kills_four_point_defect_smoke.json"
    )

    specs: list[HarnessSpec] = [
        HarnessSpec(
            name="ns_triadic_output_width_proxy",
            path=script("ns_triadic_output_width_harness.py"),
            args=(
                "--samples",
                "256",
                "--tolerance",
                "0.02",
                "--frame-model",
                "mobius",
                "--bins",
                "64",
                "--normals",
                "64",
                "--depth2-trials-per-hit",
                "2",
                "--json",
            ),
            notes=("synthetic tangent-frame proxy; diagnostic only",),
        ),
        HarnessSpec(
            name="ns_triadic_output_width_exact_if_present",
            path=script("ns_triadic_output_width_harness.py"),
            args=(
                "--samples",
                "128",
                "--tolerance",
                "0.02",
                "--frame-model",
                "exact-strain",
                "--bins",
                "48",
                "--normals",
                "48",
                "--depth2-trials-per-hit",
                "1",
                "--json",
            ),
            optional=False,
            skip_reason=(
                "scripts/ns_exact_strain_eigenbundle.py is absent; exact-strain "
                "provider not available"
            )
            if not script("ns_exact_strain_eigenbundle.py").exists()
            else None,
            notes=("runs only when exact local strain/eigenbundle provider exists",),
        ),
        HarnessSpec(
            name="ns_propagated_polarization_coherence",
            path=script("ns_propagated_polarization_coherence_harness.py"),
            args=(
                "--samples",
                "128",
                "--threshold",
                "0.08",
                "--transport-threshold",
                "0.08",
                "--normals",
                "64",
                "--input-mode",
                "mixed",
                "--second-input-mode",
                "mixed",
                "--show-worst",
                "2",
                "--json-output",
                str(ns_propagated_out),
                "--json",
            ),
            expected_json_path=ns_propagated_out,
            notes=("repaired finite NS propagated-polarization coherence smoke",),
        ),
        HarnessSpec(
            name="ns_exact_leakage_coherence_audit",
            path=script("ns_exact_leakage_coherence_audit.py"),
            args=(
                "--samples",
                "128",
                "--seed",
                "20260608",
                "--sample-rows",
                "3",
                "--json-output",
                str(ns_exact_leakage_out),
            ),
            expected_json_path=ns_exact_leakage_out,
            notes=("exact finite Leray leakage/coherence split audit",),
        ),
        HarnessSpec(
            name="ns_exact_strain_threshold_polarization_sweep",
            path=script("ns_exact_strain_threshold_polarization_sweep.py"),
            args=(
                "--tolerances",
                "0.05",
                "--polarizations",
                "canonical,seeded",
                "--seeds",
                "20260608",
                "--sample-counts",
                "96",
                "--normals",
                "48",
                "--bins",
                "48",
                "--depth2-trials-per-hit",
                "1",
                "--timeout-seconds",
                "20",
                "--json-output",
                str(ns_exact_sweep_out),
            ),
            expected_json_path=ns_exact_sweep_out,
            notes=("exact-strain threshold/polarization sweep smoke",),
        ),
        HarnessSpec(
            name="ns_sign_antisymmetry_depth_sweep",
            path=script("ns_sign_antisymmetry_depth_sweep.py"),
            args=(
                "--samples",
                "384",
                "--depth",
                "4",
                "--continuations",
                "2",
                "--max-paths-per-depth",
                "1200",
                "--zero-mode-threshold",
                "0.05",
                "--coherence-channel",
                "propagated_velocity_mean",
                "--normals",
                "128",
                "--seed",
                "20260608",
                "--json-output",
                str(ns_sign_depth_out),
            ),
            expected_json_path=ns_sign_depth_out,
            notes=("exact sign antisymmetry plus depth-k propagated survivor smoke",),
        ),
        HarnessSpec(
            name="ns_propagated_coherence_jacobian",
            path=script("ns_propagated_coherence_jacobian_harness.py"),
            args=(
                "--samples",
                "16",
                "--max-depth",
                "3",
                "--normals",
                "64",
                "--finite-diff-step",
                "1e-5",
                "--rank-tol",
                "1e-6",
                "--seed",
                "20260608",
                "--json-output",
                str(ns_jacobian_out),
            ),
            expected_json_path=ns_jacobian_out,
            notes=("finite-difference propagated coherence Jacobian smoke",),
        ),
        HarnessSpec(
            name="ns_signed_leakage_obstruction",
            path=script("ns_signed_leakage_obstruction_harness.py"),
            args=(
                "--quick",
                "--seed",
                "20260608",
                "--json-output",
                str(ns_signed_leakage_out),
                "--json",
            ),
            expected_json_path=ns_signed_leakage_out,
            notes=("classical skew-symmetry passes but triad-level leakage sign fails",),
        ),
        HarnessSpec(
            name="ns_s2_cascade_width",
            path=script("ns_s2_cascade_width_harness.py"),
            args=(
                "--samples",
                "192",
                "--continuations",
                "16",
                "--normals",
                "64",
                "--thresholds",
                "0.02,0.05,0.1",
                "--polarization-model",
                "canonical",
                "--seed",
                "20260608",
                "--json",
            ),
            expected_json_path=ns_s2_cascade_width_out,
            notes=("S2 Biot-Savart/eigenbundle cascade-width smoke; stdout JSON captured",),
        ),
        HarnessSpec(
            name="ns_leray_rank_one_symbol_audit",
            path=script("ns_leray_rank_one_symbol_audit.py"),
            args=(
                "--samples",
                "512",
                "--seed",
                "20260608",
                "--show-worst",
                "3",
                "--json-output",
                str(ns_rank_one_audit_out),
            ),
            expected_json_path=ns_rank_one_audit_out,
            notes=("finite rank-one Leray triadic classification audit",),
        ),
        HarnessSpec(
            name="ns_kappa_arcsine_law",
            path=script("ns_kappa_arcsine_law_harness.py"),
            args=(
                "--samples",
                "256",
                "--seed",
                "20260608",
                "--json",
            ),
            expected_json_path=ns_kappa_arcsine_out,
            notes=("finite S2 kappa arcsine-law smoke; stdout JSON captured",),
        ),
        HarnessSpec(
            name="ns_stretching_formula",
            path=script("ns_stretching_formula_harness.py"),
            args=(
                "--samples",
                "256",
                "--seed",
                "20260608",
                "--json",
            ),
            expected_json_path=ns_stretching_formula_out,
            notes=("finite S2 stretching identity smoke; stdout JSON captured",),
        ),
        HarnessSpec(
            name="ns_strain_mean_square_formula",
            path=script("ns_strain_mean_square_formula_harness.py"),
            args=(
                "--theta",
                "24",
                "--phi",
                "48",
                "--samples",
                "256",
                "--seed",
                "20260608",
                "--json",
            ),
            expected_json_path=ns_strain_mean_square_out,
            notes=("finite S2 mean-square strain formula smoke; stdout JSON captured",),
        ),
        HarnessSpec(
            name="ns_kappa_bias_variational",
            path=script("ns_kappa_bias_variational_harness.py"),
            args=(
                "--samples",
                "512",
                "--seed",
                "20260608",
                "--top-fraction",
                "0.08",
                "--coverage-normals",
                "32",
                "--lrt-candidate-multiplier",
                "3",
                "--json",
            ),
            expected_json_path=ns_kappa_bias_out,
            notes=("finite kappa-bias variational proxy smoke; stdout JSON captured",),
        ),
        HarnessSpec(
            name="ns_a4_four_part_proof",
            path=script("ns_a4_four_part_proof_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ns_a4_four_part_proof_out),
                "--json",
            ),
            expected_json_path=ns_a4_four_part_proof_out,
            optional=True,
            skip_reason=None
            if script("ns_a4_four_part_proof_harness.py").exists()
            else "NS A4 four-part proof harness not found",
            notes=(
                "optional A4 local derivative/coarea/LRT/error-budget proof smoke",
                "diagnostic only; no analytic theorem, NS closure, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_a4_error_budget_threshold",
            path=script("ns_a4_error_budget_threshold_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ns_a4_error_budget_threshold_out),
                "--json",
            ),
            expected_json_path=ns_a4_error_budget_threshold_out,
            optional=True,
            skip_reason=None
            if script("ns_a4_error_budget_threshold_harness.py").exists()
            else "NS A4 error-budget threshold harness not found",
            notes=(
                "optional A4 error-subtraction/r0 threshold smoke",
                "diagnostic only; no residual depletion theorem, NS closure, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_a5_kappa_bias_vanishing",
            path=script("ns_a5_kappa_bias_vanishing_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ns_a5_kappa_bias_vanishing_out),
                "--json",
            ),
            expected_json_path=ns_a5_kappa_bias_vanishing_out,
            optional=True,
            skip_reason=None
            if script("ns_a5_kappa_bias_vanishing_harness.py").exists()
            else "NS A5 kappa-bias vanishing harness not found",
            notes=(
                "optional A5 smoke for half-stretching rewrite, transfer neutrality, and |log r|^-1/2 vanishing",
                "diagnostic only; no PDE A5 theorem, no A6 theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_a6_triadic_compensated_leakage",
            path=script("ns_a6_triadic_compensated_leakage_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ns_a6_triadic_compensated_leakage_out),
                "--json",
            ),
            expected_json_path=ns_a6_triadic_compensated_leakage_out,
            optional=True,
            skip_reason=None
            if script("ns_a6_triadic_compensated_leakage_harness.py").exists()
            else "NS A6 triadic compensated leakage harness not found",
            notes=(
                "optional A6 smoke for localized ODE bookkeeping, Bony correction, and dissipation absorption",
                "diagnostic only; no PDE A6 theorem, no A7 theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_a8_annular_decay_clarification",
            path=script("ns_a8_annular_decay_clarification_harness.py"),
            args=(
                "--json-output",
                str(ns_a8_annular_decay_clarification_out),
                "--json",
            ),
            expected_json_path=ns_a8_annular_decay_clarification_out,
            optional=True,
            skip_reason=None
            if script("ns_a8_annular_decay_clarification_harness.py").exists()
            else "NS A8 annular decay clarification harness not found",
            notes=(
                "optional A8 clarification smoke for q(theta,M) < 1 and iterative defect decay",
                "diagnostic only; no PDE A8 theorem, no A9 theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_a8_full_local_defect_monotonicity",
            path=script("ns_a8_full_local_defect_monotonicity_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ns_a8_full_local_defect_monotonicity_out),
                "--json",
            ),
            expected_json_path=ns_a8_full_local_defect_monotonicity_out,
            optional=True,
            skip_reason=None
            if script("ns_a8_full_local_defect_monotonicity_harness.py").exists()
            else "NS A8 full local defect monotonicity harness not found",
            notes=(
                "optional A8 scale-recursion smoke for q(theta,M) < 1 and decay under iteration",
                "diagnostic only; no PDE A8 theorem, no A9 theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_a8_scale_monotonicity",
            path=script("ns_a8_scale_monotonicity_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ns_a8_scale_monotonicity_out),
                "--json",
            ),
            expected_json_path=ns_a8_scale_monotonicity_out,
            optional=True,
            skip_reason=None
            if script("ns_a8_scale_monotonicity_harness.py").exists()
            else "NS A8 scale monotonicity harness not found",
            notes=(
                "optional A8 special-case smoke for q(theta,M) and theta=1/2, C*M<=1/8 => q<=1/3",
                "diagnostic only; no PDE A8 theorem, no A9 theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_a7_residual_depletion_gronwall",
            path=script("ns_a7_residual_depletion_gronwall_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ns_a7_residual_depletion_gronwall_out),
                "--json",
            ),
            expected_json_path=ns_a7_residual_depletion_gronwall_out,
            optional=True,
            skip_reason=None
            if script("ns_a7_residual_depletion_gronwall_harness.py").exists()
            else "NS A7 residual depletion Gronwall harness not found",
            notes=(
                "optional A7 ODE smoke for thresholded monotone depletion below threshold",
                "diagnostic only; no PDE A7 theorem, no CKN/BKM closure, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_a9_ckn_bkm_closure",
            path=script("ns_a9_ckn_bkm_closure_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ns_a9_ckn_bkm_closure_out),
                "--json",
            ),
            expected_json_path=ns_a9_ckn_bkm_closure_out,
            optional=True,
            skip_reason=None
            if script("ns_a9_ckn_bkm_closure_harness.py").exists()
            else "NS A9 CKN/BKM closure harness not found",
            notes=(
                "optional A9 closure smoke for iterated A8 decay below a tiny threshold",
                "diagnostic only; no PDE A9 theorem and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_a9_singularity_contradiction_route",
            path=script("ns_a9_singularity_contradiction_route_harness.py"),
            args=(
                "--json-output",
                str(ns_a9_singularity_contradiction_route_out),
                "--json",
            ),
            expected_json_path=ns_a9_singularity_contradiction_route_out,
            optional=True,
            skip_reason=None
            if script("ns_a9_singularity_contradiction_route_harness.py").exists()
            else "NS A9 singularity contradiction route harness not found",
            notes=(
                "optional A9 route-normalization smoke for decay, harmonicity, elliptic regularity, and contradiction visibility",
                "diagnostic only; no PDE A9 theorem and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_a8_a9_closure_pipeline",
            path=script("ns_a8_a9_closure_pipeline_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ns_a8_a9_closure_pipeline_out),
                "--json",
            ),
            expected_json_path=ns_a8_a9_closure_pipeline_out,
            optional=True,
            skip_reason=None
            if script("ns_a8_a9_closure_pipeline_harness.py").exists()
            else "NS A8/A9 closure pipeline harness not found",
            notes=(
                "optional A8->A9 integration smoke for modeled contraction, vanishing, and local regularity handoff",
                "diagnostic only; no theorem closure, no Clay promotion, and no terminal promotion",
            ),
        ),
        HarnessSpec(
            name="ns_typeI_selfsimilar_kappa_bias",
            path=script("ns_typeI_selfsimilar_kappa_bias_harness.py"),
            args=(
                "--samples",
                "512",
                "--shells",
                "8",
                "--seed",
                "20260608",
                "--profile",
                "all",
                "--penalty-scale",
                "0.08",
                "--json-output",
                str(ns_typei_kappa_bias_out),
                "--json",
            ),
            expected_json_path=ns_typei_kappa_bias_out,
            optional=True,
            skip_reason=None
            if script("ns_typeI_selfsimilar_kappa_bias_harness.py").exists()
            else "Type-I/self-similar kappa-bias balance harness not found",
            notes=(
                "optional Gaussian/Type-I self-similar kappa-bias balance proxy smoke",
                "diagnostic only; no Type-I theorem, Abel measure construction, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_abel_triadic_measure_proxy",
            path=script("ns_abel_triadic_measure_proxy_harness.py"),
            args=(
                "--samples",
                "384",
                "--depths",
                "6",
                "--abel-rho",
                "0.82",
                "--coverage-normals",
                "48",
                "--bins",
                "16",
                "--seed",
                "20260608",
                "--json-output",
                str(ns_abel_triadic_measure_proxy_out),
                "--json",
            ),
            expected_json_path=ns_abel_triadic_measure_proxy_out,
            optional=True,
            skip_reason=None
            if script("ns_abel_triadic_measure_proxy_harness.py").exists()
            else "NS Abel triadic measure proxy harness not found",
            notes=(
                "optional Abel-weighted triadic defect-measure proxy smoke",
                "diagnostic only; no Abel defect-measure construction or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_kappa_bias_profile_sweep",
            path=script("ns_kappa_bias_profile_sweep.py"),
            args=(
                "--quick",
                "--samples",
                "900",
                "--seed",
                "20260608",
                "--json-output",
                str(ns_kappa_bias_profile_sweep_out),
                "--json",
            ),
            expected_json_path=ns_kappa_bias_profile_sweep_out,
            optional=True,
            skip_reason=None
            if script("ns_kappa_bias_profile_sweep.py").exists()
            else "NS kappa-bias profile sweep harness not found",
            notes=(
                "optional kappa-bias profile sensitivity sweep smoke",
                "diagnostic only; no Type-I kappa-bias theorem or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_gaussian_selfsimilar_kappa_bias_balance",
            path=script("ns_gaussian_selfsimilar_kappa_bias_balance_harness.py"),
            args=(
                "--samples",
                "512",
                "--shells",
                "8",
                "--seed",
                "20260608",
                "--json-output",
                str(ns_gaussian_balance_out),
                "--json",
            ),
            expected_json_path=ns_gaussian_balance_out,
            optional=True,
            skip_reason=None
            if script("ns_gaussian_selfsimilar_kappa_bias_balance_harness.py").exists()
            else "corrected Gaussian self-similar kappa-bias balance harness not found",
            notes=(
                "optional corrected Gaussian balance smoke for 1 <= 4*bias + drift",
                "diagnostic only; no Abel measure construction, Type-I theorem, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_transfer_operator_bias_neutrality",
            path=script("ns_transfer_operator_bias_neutrality_harness.py"),
            args=(
                "--samples",
                "512",
                "--seed",
                "20260608",
                "--json-output",
                str(ns_transfer_operator_bias_out),
                "--json",
            ),
            expected_json_path=ns_transfer_operator_bias_out,
            optional=True,
            skip_reason=None
            if script("ns_transfer_operator_bias_neutrality_harness.py").exists()
            else "NS transfer-operator bias neutrality harness not found",
            notes=(
                "optional NS-F7 finite transfer-operator bias-neutrality smoke",
                "diagnostic only; tests conditional independence baseline and no PDE/Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_abel_triadic_stationarity_proxy",
            path=script("ns_abel_triadic_stationarity_proxy_harness.py"),
            args=(
                "--samples",
                "512",
                "--seed",
                "20260608",
                "--json-output",
                str(ns_abel_triadic_stationarity_proxy_out),
                "--json",
            ),
            expected_json_path=ns_abel_triadic_stationarity_proxy_out,
            optional=True,
            skip_reason=None
            if script("ns_abel_triadic_stationarity_proxy_harness.py").exists()
            else "NS Abel triadic stationarity proxy harness not found",
            notes=(
                "optional Abel triadic stationarity proxy smoke",
                "diagnostic only; no Abel measure construction, stationarity theorem, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_a1_type_i_abel_mass_route",
            path=script("ns_a1_type_i_abel_mass_route_harness.py"),
            args=(
                "--json-output",
                str(ns_a1_type_i_abel_mass_route_out),
                "--json",
            ),
            expected_json_path=ns_a1_type_i_abel_mass_route_out,
            optional=True,
            skip_reason=None
            if script("ns_a1_type_i_abel_mass_route_harness.py").exists()
            else "NS A1 Type-I/Lorentz to Abel mass route harness not found",
            notes=(
                "optional A1 route-normalization smoke for shell-mass to Abel averaging",
                "diagnostic only; no PDE A1 theorem, no Abel defect-measure construction, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_a1_type_i_abel_mass_theorem",
            path=script("ns_a1_type_i_abel_mass_theorem_harness.py"),
            args=(
                "--json-output",
                str(ns_a1_type_i_abel_mass_theorem_out),
                "--json",
            ),
            expected_json_path=ns_a1_type_i_abel_mass_theorem_out,
            optional=True,
            skip_reason=None
            if script("ns_a1_type_i_abel_mass_theorem_harness.py").exists()
            else "NS A1 theorem-facing Abel measure harness not found",
            notes=(
                "optional A1 theorem-facing smoke for ESS plus shell/Abel measure bookkeeping",
                "diagnostic only; no PDE Abel measure theorem, no Clay promotion, and no terminal promotion",
            ),
        ),
        HarnessSpec(
            name="ns_a2_near_diagonal_coifman_meyer",
            path=script("ns_a2_near_diagonal_coifman_meyer_harness.py"),
            args=(
                "--json-output",
                str(ns_a2_near_diagonal_coifman_meyer_out),
                "--json",
            ),
            expected_json_path=ns_a2_near_diagonal_coifman_meyer_out,
            optional=True,
            skip_reason=None
            if script("ns_a2_near_diagonal_coifman_meyer_harness.py").exists()
            else "NS A2 near-diagonal Coifman-Meyer harness not found",
            notes=(
                "optional A2 route-normalization smoke for the tight 2^min(j,k) bound",
                "diagnostic only; no theorem-level Coifman-Meyer estimate and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_a2_near_diagonal_coifman_meyer_theorem",
            path=script("ns_a2_near_diagonal_coifman_meyer_theorem_harness.py"),
            args=(
                "--json-output",
                str(ns_a2_near_diagonal_coifman_meyer_theorem_out),
                "--json",
            ),
            expected_json_path=ns_a2_near_diagonal_coifman_meyer_theorem_out,
            optional=True,
            skip_reason=None
            if script("ns_a2_near_diagonal_coifman_meyer_theorem_harness.py").exists()
            else "NS A2 theorem-facing near-diagonal harness not found",
            notes=(
                "optional A2 theorem-facing smoke for near-diagonal shell dominance and delta_r bookkeeping",
                "diagnostic only; no PDE Coifman-Meyer theorem, no A5 transfer theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_stationarity_rate_proxy",
            path=script("ns_stationarity_rate_proxy_harness.py"),
            args=(
                "--depths",
                "8",
                "--min-depth",
                "2",
                "--json-output",
                str(ns_stationarity_rate_proxy_out),
                "--json",
            ),
            expected_json_path=ns_stationarity_rate_proxy_out,
            optional=True,
            skip_reason=None
            if script("ns_stationarity_rate_proxy_harness.py").exists()
            else "NS stationarity-rate proxy harness not found",
            notes=(
                "optional stationarity-rate proxy smoke with log(1/r)^(-1/2) theta and bad nondecaying control",
                "diagnostic only; no stationarity theorem, PDE measure construction, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_bounded_abel_mass_proxy",
            path=script("ns_bounded_abel_mass_proxy_harness.py"),
            args=(
                "--shells",
                "18",
                "--window",
                "7",
                "--abel-rho",
                "0.78",
                "--bad-growth",
                "0.18",
                "--json-output",
                str(ns_bounded_abel_mass_proxy_out),
                "--json",
            ),
            expected_json_path=ns_bounded_abel_mass_proxy_out,
            optional=True,
            skip_reason=None
            if script("ns_bounded_abel_mass_proxy_harness.py").exists()
            else "NS bounded Abel-mass proxy harness not found",
            notes=(
                "optional A1 bounded Abel/log-window mass proxy smoke with deliberate bad profile",
                "diagnostic only; no PDE Abel measure construction, bounded-mass theorem, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_biot_savart_shell_localization_proxy",
            path=script("ns_biot_savart_shell_localization_proxy_harness.py"),
            args=(
                "--levels",
                "12",
                "--sweeps",
                "8",
                "--json-output",
                str(ns_biot_savart_shell_localization_proxy_out),
                "--json",
            ),
            expected_json_path=ns_biot_savart_shell_localization_proxy_out,
            optional=True,
            skip_reason=None
            if script("ns_biot_savart_shell_localization_proxy_harness.py").exists()
            else "NS Biot-Savart shell-localization proxy harness not found",
            notes=(
                "optional A6.2 Biot-Savart shell-localization proxy for same-shell multiplier ownership and off-shell tail decay",
                "diagnostic only; no Calderon-Zygmund shell-localization theorem, A6 theorem, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_lrt_fourier_output_coupling_proxy",
            path=script("ns_lrt_fourier_output_coupling_proxy_harness.py"),
            args=(
                "--frames",
                "14",
                "--sweeps",
                "8",
                "--json-output",
                str(ns_lrt_fourier_output_coupling_proxy_out),
                "--json",
            ),
            expected_json_path=ns_lrt_fourier_output_coupling_proxy_out,
            optional=True,
            skip_reason=None
            if script("ns_lrt_fourier_output_coupling_proxy_harness.py").exists()
            else "NS LRT Fourier-output coupling proxy harness not found",
            notes=(
                "optional A4 LRT physical-to-Fourier output-support coupling proxy for Whitney/frame/localization components",
                "diagnostic only; no LRT coupling theorem, output-support theorem, A6 theorem, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_bony_paraproduct_a6_repair_proxy",
            path=script("ns_bony_paraproduct_a6_repair_proxy_harness.py"),
            args=(
                "--levels",
                "12",
                "--sweeps",
                "8",
                "--json-output",
                str(ns_bony_paraproduct_a6_repair_proxy_out),
                "--json",
            ),
            expected_json_path=ns_bony_paraproduct_a6_repair_proxy_out,
            optional=True,
            skip_reason=None
            if script("ns_bony_paraproduct_a6_repair_proxy_harness.py").exists()
            else "NS Bony paraproduct A6 repair proxy harness not found",
            notes=(
                "optional corrected A6.2 Bony paraproduct repair proxy separating naive O(1) off-shell failure from corrected routing",
                "diagnostic only; no paraproduct theorem, A6 theorem, residual depletion, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_pointwise_to_abel_averaging_proxy",
            path=script("ns_pointwise_to_abel_averaging_proxy_harness.py"),
            args=(
                "--shells",
                "18",
                "--samples-per-shell",
                "128",
                "--window",
                "7",
                "--abel-rho",
                "0.76",
                "--offdiag-scale",
                "0.10",
                "--lln-multiplier",
                "3.0",
                "--seed",
                "20260608",
                "--json-output",
                str(ns_pointwise_to_abel_proxy_out),
                "--json",
            ),
            expected_json_path=ns_pointwise_to_abel_proxy_out,
            optional=True,
            skip_reason=None
            if script("ns_pointwise_to_abel_averaging_proxy_harness.py").exists()
            else "NS pointwise-to-Abel averaging proxy harness not found",
            notes=(
                "optional A6 pointwise-to-Abel averaging proxy smoke with deliberate correlated bad profile",
                "diagnostic only; no Abel LLN, compensated leakage identity, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_localization_pressure_commutator_proxy",
            path=script("ns_localization_pressure_commutator_proxy_harness.py"),
            args=(
                "--refinements",
                "9",
                "--json-output",
                str(ns_localization_pressure_proxy_out),
                "--json",
            ),
            expected_json_path=ns_localization_pressure_proxy_out,
            optional=True,
            skip_reason=None
            if script("ns_localization_pressure_commutator_proxy_harness.py").exists()
            else "NS localization pressure/commutator proxy harness not found",
            notes=(
                "optional A6 localization/pressure commutator proxy with deliberate bad tail and cutoff cases",
                "diagnostic only; no pressure localization theorem, pointwise-to-Abel theorem, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_pressure_tail_absorption_proxy",
            path=script("ns_pressure_tail_absorption_proxy_harness.py"),
            args=(
                "--depths",
                "12",
                "--samples",
                "1600",
                "--tolerance",
                "0.008",
                "--bad-floor",
                "0.025",
                "--json-output",
                str(ns_pressure_tail_absorption_proxy_out),
                "--json",
            ),
            expected_json_path=ns_pressure_tail_absorption_proxy_out,
            optional=True,
            skip_reason=None
            if script("ns_pressure_tail_absorption_proxy_harness.py").exists()
            else "NS pressure-tail absorption proxy harness not found",
            notes=(
                "optional A6 pressure-tail absorption proxy with bad harmonic-tail, annular-plateau, and gradient profiles",
                "diagnostic only; no pressure-tail theorem, pressure commutator theorem, A6 theorem, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_cutoff_riesz_commutator_kernel_proxy",
            path=script("ns_cutoff_riesz_commutator_kernel_proxy_harness.py"),
            args=(
                "--min-j",
                "4",
                "--max-j",
                "9",
                "--samples",
                "700",
                "--tolerance",
                "0.0018",
                "--bad-floor",
                "0.005",
                "--json-output",
                str(ns_cutoff_riesz_commutator_kernel_proxy_out),
                "--json",
            ),
            expected_json_path=ns_cutoff_riesz_commutator_kernel_proxy_out,
            optional=True,
            skip_reason=None
            if script("ns_cutoff_riesz_commutator_kernel_proxy_harness.py").exists()
            else "NS cutoff/Riesz commutator kernel proxy harness not found",
            notes=(
                "optional A6 cutoff/Riesz commutator kernel proxy with cancellation, annulus separation, and bad rough/no-cancellation/touching-core cases",
                "diagnostic only; no cutoff/Riesz commutator estimate, pressure theorem, A6 theorem, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_harmonic_pressure_tail_decay_proxy",
            path=script("ns_harmonic_pressure_tail_decay_proxy_harness.py"),
            args=(
                "--depths",
                "12",
                "--tolerance",
                "0.006",
                "--bad-floor",
                "0.025",
                "--json-output",
                str(ns_harmonic_pressure_tail_decay_proxy_out),
                "--json",
            ),
            expected_json_path=ns_harmonic_pressure_tail_decay_proxy_out,
            optional=True,
            skip_reason=None
            if script("ns_harmonic_pressure_tail_decay_proxy_harness.py").exists()
            else "NS harmonic pressure-tail decay proxy harness not found",
            notes=(
                "optional A6 harmonic pressure-tail proxy with mean-subtraction, annular separation, and moment-cancellation controls",
                "diagnostic only; no harmonic pressure-tail theorem, A6 theorem, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_pressure_localization_subbudget_proxy",
            path=script("ns_pressure_localization_subbudget_proxy_harness.py"),
            args=(
                "--levels",
                "12",
                "--tolerance",
                "0.01",
                "--bad-floor",
                "0.03",
                "--json-output",
                str(ns_pressure_localization_subbudget_proxy_out),
                "--json",
            ),
            expected_json_path=ns_pressure_localization_subbudget_proxy_out,
            optional=True,
            skip_reason=None
            if script("ns_pressure_localization_subbudget_proxy_harness.py").exists()
            else "NS pressure localization sub-budget proxy harness not found",
            notes=(
                "optional A6 pressure-localization sub-budget proxy aggregating cutoff/Riesz, local CZ, harmonic tail, pressure tail, annular cutoff, epsilon absorption, and Abel recentering",
                "diagnostic only; no pressure localization theorem, A6 theorem, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_pressure_subbudget_component_sensitivity",
            path=script("ns_pressure_subbudget_component_sensitivity_harness.py"),
            args=(
                "--levels",
                "12",
                "--sweeps",
                "8",
                "--json-output",
                str(ns_pressure_subbudget_component_sensitivity_out),
                "--json",
            ),
            expected_json_path=ns_pressure_subbudget_component_sensitivity_out,
            optional=True,
            skip_reason=None
            if script("ns_pressure_subbudget_component_sensitivity_harness.py").exists()
            else "NS pressure sub-budget component-sensitivity harness not found",
            notes=(
                "optional A6 pressure-localization component-sensitivity sweep across seven sub-budgets",
                "diagnostic only; no component-sensitivity theorem, pressure sub-budget closure, A6 theorem, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_a6_error_budget_proxy",
            path=script("ns_a6_error_budget_proxy_harness.py"),
            args=(
                "--min-depth",
                "6",
                "--max-depth",
                "48",
                "--tolerance",
                "0.075",
                "--bad-floor",
                "0.115",
                "--json-output",
                str(ns_a6_error_budget_proxy_out),
                "--json",
            ),
            expected_json_path=ns_a6_error_budget_proxy_out,
            optional=True,
            skip_reason=None
            if script("ns_a6_error_budget_proxy_harness.py").exists()
            else "NS A6 error-budget proxy harness not found",
            notes=(
                "optional A6 aggregate error-budget proxy with seven component budgets",
                "diagnostic only; no aggregate A6 error theorem, leakage identity, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_cascade_depth2_proxy",
            path=script("ns_cascade_depth2_harness.py"),
            args=(
                "--pairs",
                "256",
                "--continuations",
                "24",
                "--normals",
                "64",
                "--zero-threshold",
                "0.03",
                "--depth2-threshold",
                "0.03",
                "--show",
                "3",
                "--json",
            ),
            notes=("depth-2 cascade closure smoke probe",),
        ),
        HarnessSpec(
            name="ns_leakage_square_toy",
            path=script("ns_leakage_square_toy_harness.py"),
            args=("--triads", "48"),
            notes=("finite triadic Leray bookkeeping; no PDE sign proof",),
        ),
        HarnessSpec(
            name="ym_bt_tree_spectral_gap",
            path=script("ym_bt_tree_spectral_gap_harness.py"),
            args=(
                "--p",
                "2,3",
                "--depths",
                "2,3",
                "--boundary",
                "induced,full-degree",
                "--laplacian",
                "normalized",
                "--max-nodes",
                "300",
                "--out",
                str(ym_bt_out),
                "--json",
            ),
            expected_json_path=ym_bt_out,
            notes=("finite tree boundary-convention smoke",),
        ),
        HarnessSpec(
            name="ym_bt_boundary_depth_regression",
            path=script("ym_bt_boundary_depth_regression.py"),
            args=(
                "--p",
                "2,3",
                "--depths",
                "2,3,4",
                "--boundary",
                "induced,full-degree",
                "--laplacian",
                "normalized",
                "--max-nodes",
                "700",
                "--out",
                str(ym_boundary_regression_out),
                "--harness-out",
                str(ym_boundary_regression_harness_out),
            ),
            expected_json_path=ym_boundary_regression_out,
            notes=("YM BT boundary-depth regression smoke",),
        ),
        HarnessSpec(
            name="ym_bt_dobrushin_influence",
            path=script("ym_bt_dobrushin_influence_harness.py"),
            args=(
                "--p-values",
                "2,3,7",
                "--betas",
                "0.05,0.1,0.2",
                "--depth",
                "2",
                "--out",
                str(dobrushin_out),
            ),
            expected_json_path=dobrushin_out,
            notes=("toy influence proxy only",),
        ),
        HarnessSpec(
            name="ym_finite_selfadjoint_hamiltonian_proxy",
            path=script("ym_finite_selfadjoint_hamiltonian_proxy_harness.py"),
            args=(
                "--dimension",
                "6",
                "--quotient-dimension",
                "4",
                "--json-output",
                str(ym_selfadjoint_proxy_out),
                "--json",
            ),
            expected_json_path=ym_selfadjoint_proxy_out,
            optional=True,
            skip_reason=None
            if script("ym_finite_selfadjoint_hamiltonian_proxy_harness.py").exists()
            else "YM finite self-adjoint Hamiltonian proxy harness not found",
            notes=(
                "finite self-adjoint Hamiltonian proxy with bad nonsymmetric and domain-unstable cases",
                "diagnostic only; no YM Hamiltonian theorem, OS transfer, continuum gap, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_hamiltonian_domination_proxy",
            path=script("ym_hamiltonian_domination_proxy_harness.py"),
            args=(
                "--dimension",
                "5",
                "--quotient-dimension",
                "3",
                "--json-output",
                str(ym_hamiltonian_domination_proxy_out),
                "--json",
            ),
            expected_json_path=ym_hamiltonian_domination_proxy_out,
            optional=True,
            skip_reason=None
            if script("ym_hamiltonian_domination_proxy_harness.py").exists()
            else "YM Hamiltonian domination proxy harness not found",
            notes=(
                "finite quotient-matrix proxy for H >= c1 Delta + c2 Hol - E",
                "diagnostic only; no Hamiltonian domination theorem, OS transfer, continuum gap, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_domination_spectral_margin_proxy",
            path=script("ym_domination_spectral_margin_proxy_harness.py"),
            args=(
                "--dimension",
                "6",
                "--quotient-dimension",
                "4",
                "--json-output",
                str(ym_domination_spectral_margin_proxy_out),
                "--json",
            ),
            expected_json_path=ym_domination_spectral_margin_proxy_out,
            optional=True,
            skip_reason=None
            if script("ym_domination_spectral_margin_proxy_harness.py").exists()
            else "YM domination spectral-margin proxy harness not found",
            notes=(
                "finite spectral-margin proxy for YM domination error budget with weak kinetic, missing holonomy, and pollution bad cases",
                "diagnostic only; no Hamiltonian domination theorem, OS transfer, continuum gap, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_spectral_margin_boundary_sensitivity",
            path=script("ym_spectral_margin_boundary_sensitivity_harness.py"),
            args=(
                "--dimension",
                "6",
                "--quotient-dimension",
                "4",
                "--sweeps",
                "8",
                "--json-output",
                str(ym_spectral_margin_boundary_sensitivity_out),
                "--json",
            ),
            expected_json_path=ym_spectral_margin_boundary_sensitivity_out,
            optional=True,
            skip_reason=None
            if script("ym_spectral_margin_boundary_sensitivity_harness.py").exists()
            else "YM spectral-margin boundary-sensitivity harness not found",
            notes=(
                "optional finite spectral-margin boundary-sensitivity sweep for kinetic, holonomy, error, and pollution budgets",
                "diagnostic only; no spectral-margin theorem, Hamiltonian domination, OS transfer, continuum gap, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_killing_boundary_self_adjointness_proxy",
            path=script("ym_killing_boundary_self_adjointness_proxy_harness.py"),
            args=(
                "--dimension",
                "6",
                "--quotient-dimension",
                "4",
                "--sweeps",
                "8",
                "--json-output",
                str(ym_killing_boundary_self_adjointness_proxy_out),
                "--json",
            ),
            expected_json_path=ym_killing_boundary_self_adjointness_proxy_out,
            optional=True,
            skip_reason=None
            if script("ym_killing_boundary_self_adjointness_proxy_harness.py").exists()
            else "YM Killing boundary self-adjointness proxy harness not found",
            notes=(
                "optional finite YM Killing/full-degree boundary domain proxy for symmetry defect, gauge-null leakage, and spectral margin",
                "diagnostic only; no finite self-adjointness theorem, Hamiltonian domination, OS transfer, continuum gap, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_seiler_continuum_route",
            path=script("ym_seiler_continuum_route_harness.py"),
            args=(
                "--json-output",
                str(ym_seiler_continuum_route_out),
                "--json",
            ),
            expected_json_path=ym_seiler_continuum_route_out,
            optional=True,
            skip_reason=None
            if script("ym_seiler_continuum_route_harness.py").exists()
            else "YM Seiler/continuum route harness not found",
            notes=(
                "optional YM Seiler 1982 and BT->4D continuum route smoke",
                "diagnostic only; no continuum mass gap, no OS/Wightman theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_continuum_uniform_rho_bound",
            path=script("ym_continuum_uniform_rho_bound_harness.py"),
            args=(
                "--json-output",
                str(ym_continuum_uniform_rho_bound_out),
                "--json",
            ),
            expected_json_path=ym_continuum_uniform_rho_bound_out,
            optional=True,
            skip_reason=None
            if script("ym_continuum_uniform_rho_bound_harness.py").exists()
            else "YM continuum uniform rho bound harness not found",
            notes=(
                "optional YM continuum rho-density smoke from McKay weak limits plus Casimir shift budget",
                "diagnostic only; no continuum rho theorem, no mass-gap theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_continuum_uniform_leakage_bound",
            path=script("ym_continuum_uniform_leakage_bound_harness.py"),
            args=(
                "--json-output",
                str(ym_continuum_uniform_leakage_bound_out),
                "--json",
            ),
            expected_json_path=ym_continuum_uniform_leakage_bound_out,
            optional=True,
            skip_reason=None
            if script("ym_continuum_uniform_leakage_bound_harness.py").exists()
            else "YM continuum uniform leakage bound harness not found",
            notes=(
                "optional YM continuum leakage-decay smoke from holonomy floor plus BT boundary ratio",
                "diagnostic only; no continuum leakage theorem, no mass-gap theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_hyperbolic_shimura_to_euclidean_universality",
            path=script("ym_hyperbolic_shimura_to_euclidean_universality_harness.py"),
            args=(
                "--json-output",
                str(ym_hyperbolic_shimura_to_euclidean_universality_out),
                "--json",
            ),
            expected_json_path=ym_hyperbolic_shimura_to_euclidean_universality_out,
            optional=True,
            skip_reason=None
            if script("ym_hyperbolic_shimura_to_euclidean_universality_harness.py").exists()
            else "YM hyperbolic/Shimura to Euclidean universality harness not found",
            notes=(
                "optional YM BT-to-Euclidean gap-transfer smoke with Weyl perturbation budget",
                "diagnostic only; no BT-to-Euclidean universality theorem, no RG transfer, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_killing_boundary_flux_pairing",
            path=script("ym_killing_boundary_flux_pairing_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_killing_boundary_flux_pairing_out),
                "--json",
            ),
            expected_json_path=ym_killing_boundary_flux_pairing_out,
            optional=True,
            skip_reason=None
            if script("ym_killing_boundary_flux_pairing_harness.py").exists()
            else "YM Killing boundary flux pairing harness not found",
            notes=(
                "optional narrow YM-1 boundary-pairing smoke for opposite-face involution, weights, orientations, and flux cancellation",
                "diagnostic only; no finite self-adjointness theorem, Hamiltonian domination, OS transfer, continuum gap, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_killing_boundary_theorem",
            path=script("ym_killing_boundary_theorem_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_killing_boundary_theorem_out),
                "--json",
            ),
            expected_json_path=ym_killing_boundary_theorem_out,
            optional=True,
            skip_reason=None
            if script("ym_killing_boundary_theorem_harness.py").exists()
            else "YM Killing boundary theorem harness not found",
            notes=(
                "optional lightweight theorem-content smoke for the standalone YM-1 receipt",
                "diagnostic only; no finite self-adjointness theorem, Hamiltonian domination, OS transfer, continuum gap, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_opposite_face_involution_theorem",
            path=script("ym_opposite_face_involution_theorem_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_opposite_face_involution_theorem_out),
                "--json",
            ),
            expected_json_path=ym_opposite_face_involution_theorem_out,
            optional=True,
            skip_reason=None
            if script("ym_opposite_face_involution_theorem_harness.py").exists()
            else "YM opposite-face involution theorem harness not found",
            notes=(
                "optional lightweight YM-1 child smoke for opposite-face involution, axis preservation, orientation cancellation, and weight matching",
                "diagnostic only; no finite theorem, Hamiltonian domination, OS transfer, continuum gap, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_flux_cancellation_theorem",
            path=script("ym_flux_cancellation_theorem_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_flux_cancellation_theorem_out),
                "--json",
            ),
            expected_json_path=ym_flux_cancellation_theorem_out,
            optional=True,
            skip_reason=None
            if script("ym_flux_cancellation_theorem_harness.py").exists()
            else "YM flux cancellation theorem harness not found",
            notes=(
                "optional lightweight YM-1 child smoke for paired boundary flux cancellation",
                "diagnostic only; no finite theorem, Hamiltonian domination, OS transfer, continuum gap, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_gauge_quotient_domain",
            path=script("ym_gauge_quotient_domain_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_gauge_quotient_domain_out),
                "--json",
            ),
            expected_json_path=ym_gauge_quotient_domain_out,
            optional=True,
            skip_reason=None
            if script("ym_gauge_quotient_domain_harness.py").exists()
            else "YM gauge quotient domain harness not found",
            notes=(
                "optional YM-1 quotient-domain smoke for constant gauge mode, projection, quotient preservation, and quotient self-adjointness",
                "diagnostic only; no finite theorem, domination, OS transfer, continuum gap, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_gauge_quotient_descent_theorem",
            path=script("ym_gauge_quotient_descent_theorem_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_gauge_quotient_descent_theorem_out),
                "--json",
            ),
            expected_json_path=ym_gauge_quotient_descent_theorem_out,
            optional=True,
            skip_reason=None
            if script("ym_gauge_quotient_descent_theorem_harness.py").exists()
            else "YM gauge quotient descent theorem harness not found",
            notes=(
                "optional lightweight YM-1 child smoke for gauge-null elimination, representative independence, and quotient descent",
                "diagnostic only; no finite theorem, domination, OS transfer, continuum gap, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_quotient_symmetry_theorem",
            path=script("ym_quotient_symmetry_theorem_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_quotient_symmetry_theorem_out),
                "--json",
            ),
            expected_json_path=ym_quotient_symmetry_theorem_out,
            optional=True,
            skip_reason=None
            if script("ym_quotient_symmetry_theorem_harness.py").exists()
            else "YM quotient symmetry theorem harness not found",
            notes=(
                "optional lightweight YM-1 child smoke for quotient symmetry, null-mode elimination, and nonnegative Rayleigh behavior",
                "diagnostic only; no finite theorem, domination, OS transfer, continuum gap, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_killing_boundary_child_composite",
            path=script("ym_killing_boundary_child_composite_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_killing_boundary_child_composite_out),
                "--json",
            ),
            expected_json_path=ym_killing_boundary_child_composite_out,
            optional=True,
            skip_reason=None
            if script("ym_killing_boundary_child_composite_harness.py").exists()
            else "YM killing boundary child composite harness not found",
            notes=(
                "optional lightweight YM-1 composite smoke joining opposite-face, flux, descent, and quotient symmetry children",
                "diagnostic only; no finite theorem, domination, OS transfer, continuum gap, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_selfadjoint_to_domination_precondition",
            path=script("ym_selfadjoint_to_domination_precondition_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_selfadjoint_to_domination_precondition_out),
                "--json",
            ),
            expected_json_path=ym_selfadjoint_to_domination_precondition_out,
            optional=True,
            skip_reason=None
            if script("ym_selfadjoint_to_domination_precondition_harness.py").exists()
            else "YM self-adjointness to domination precondition harness not found",
            notes=(
                "optional lightweight YM composite smoke from self-adjoint quotient input into domination preconditions",
                "diagnostic only; no domination theorem, spectral margin theorem, or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_domination_spectral_margin_route",
            path=script("ym_domination_spectral_margin_route_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_domination_spectral_margin_route_out),
                "--json",
            ),
            expected_json_path=ym_domination_spectral_margin_route_out,
            optional=True,
            skip_reason=None
            if script("ym_domination_spectral_margin_route_harness.py").exists()
            else "YM domination/spectral-margin route harness not found",
            notes=(
                "optional lightweight YM route smoke from domination preconditions through positive holonomy into the spectral-margin socket",
                "diagnostic only; no domination theorem, no finite gap theorem, no continuum gap, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_continuum_nospectral_route",
            path=script("ym_continuum_nospectral_route_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_continuum_nospectral_route_out),
                "--json",
            ),
            expected_json_path=ym_continuum_nospectral_route_out,
            optional=True,
            skip_reason=None
            if script("ym_continuum_nospectral_route_harness.py").exists()
            else "YM continuum/no-spectral route harness not found",
            notes=(
                "optional lightweight YM route smoke from spectral margin through continuum transfer into the no-spectral-pollution socket",
                "diagnostic only; no no-spectral-pollution theorem, no Wightman theorem, no continuum mass-gap theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_orientation_sign_cancellation",
            path=script("ym_orientation_sign_cancellation_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_orientation_sign_cancellation_out),
                "--json",
            ),
            expected_json_path=ym_orientation_sign_cancellation_out,
            optional=True,
            skip_reason=None
            if script("ym_orientation_sign_cancellation_harness.py").exists()
            else "YM orientation-sign cancellation harness not found",
            notes=(
                "optional explicit YM-1.3 paired orientation-sign cancellation smoke",
                "diagnostic only; no Green identity theorem, no self-adjointness theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_spectral_gap_explicit_constant",
            path=script("ym_spectral_gap_explicit_constant_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_spectral_gap_explicit_constant_out),
                "--json",
            ),
            expected_json_path=ym_spectral_gap_explicit_constant_out,
            optional=True,
            skip_reason=None
            if script("ym_spectral_gap_explicit_constant_harness.py").exists()
            else "YM spectral-gap explicit constant harness not found",
            notes=(
                "optional explicit finite spectral-gap constant smoke gamma_d >= Casimir_min/4",
                "diagnostic only; no continuum gap theorem, no OS/Wightman theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_step_scaling_global_bound",
            path=script("ym_step_scaling_global_bound_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_step_scaling_global_bound_out),
                "--json",
            ),
            expected_json_path=ym_step_scaling_global_bound_out,
            optional=True,
            skip_reason=None
            if script("ym_step_scaling_global_bound_harness.py").exists()
            else "YM step-scaling global-bound harness not found",
            notes=(
                "optional RG step-scaling global-bound smoke with running-coupling compensation",
                "diagnostic only; no reflection-positivity theorem, no final continuum mass-gap theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_reflection_positivity_boundary_convention",
            path=script("ym_reflection_positivity_boundary_convention_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_reflection_positivity_boundary_convention_out),
                "--json",
            ),
            expected_json_path=ym_reflection_positivity_boundary_convention_out,
            optional=True,
            skip_reason=None
            if script("ym_reflection_positivity_boundary_convention_harness.py").exists()
            else "YM reflection-positivity boundary-convention harness not found",
            notes=(
                "optional boundary-pairing/theta-compatibility smoke for the YM reflection-positivity convention",
                "diagnostic only; no reflection-positivity theorem, no OS/Wightman theorem, no final mass-gap theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_os_wightman_massgap_route",
            path=script("ym_os_wightman_massgap_route_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_os_wightman_massgap_route_out),
                "--json",
            ),
            expected_json_path=ym_os_wightman_massgap_route_out,
            optional=True,
            skip_reason=None
            if script("ym_os_wightman_massgap_route_harness.py").exists()
            else "YM OS/Wightman/final-mass-gap route harness not found",
            notes=(
                "optional lightweight YM route smoke from no-spectral-pollution through reflection positivity and OS/Wightman into final mass-gap assembly",
                "diagnostic only; no OS/Wightman theorem, no final continuum mass-gap theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_reflection_positivity_child",
            path=script("ym_reflection_positivity_child_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_reflection_positivity_child_out),
                "--json",
            ),
            expected_json_path=ym_reflection_positivity_child_out,
            optional=True,
            skip_reason=None
            if script("ym_reflection_positivity_child_harness.py").exists()
            else "YM reflection-positivity child harness not found",
            notes=(
                "optional lightweight YM reflection-positivity child composite smoke",
                "diagnostic only; no reflection-positivity theorem, no OS/Wightman theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_final_assembly_clay_blocker",
            path=script("ym_final_assembly_clay_blocker_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_final_assembly_clay_blocker_out),
                "--json",
            ),
            expected_json_path=ym_final_assembly_clay_blocker_out,
            optional=True,
            skip_reason=None
            if script("ym_final_assembly_clay_blocker_harness.py").exists()
            else "YM final-assembly Clay-blocker harness not found",
            notes=(
                "optional lightweight YM final-assembly to Clay-authority blocker smoke",
                "diagnostic only; no final continuum mass-gap theorem, no external-acceptance theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_reflection_positivity_consolidation",
            path=script("ym_reflection_positivity_consolidation_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_reflection_positivity_consolidation_out),
                "--json",
            ),
            expected_json_path=ym_reflection_positivity_consolidation_out,
            optional=True,
            skip_reason=None
            if script("ym_reflection_positivity_consolidation_harness.py").exists()
            else "YM reflection-positivity consolidation harness not found",
            notes=(
                "optional lightweight YM reflection-positivity consolidation smoke",
                "diagnostic only; no reflection-positivity theorem, no OS/Wightman theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_final_authority_packaging",
            path=script("ym_final_authority_packaging_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_final_authority_packaging_out),
                "--json",
            ),
            expected_json_path=ym_final_authority_packaging_out,
            optional=True,
            skip_reason=None
            if script("ym_final_authority_packaging_harness.py").exists()
            else "YM final-authority packaging harness not found",
            notes=(
                "optional lightweight YM final-authority packaging smoke",
                "diagnostic only; no external-acceptance theorem, no final continuum authority theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_reflection_positivity_spatial_tau_theta_commutativity",
            path=script("ym_reflection_positivity_spatial_tau_theta_commutativity_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_reflection_positivity_spatial_tau_theta_commutativity_out),
                "--json",
            ),
            expected_json_path=ym_reflection_positivity_spatial_tau_theta_commutativity_out,
            optional=True,
            skip_reason=None
            if script("ym_reflection_positivity_spatial_tau_theta_commutativity_harness.py").exists()
            else "YM RP tau/theta commutativity harness not found",
            notes=(
                "optional exact YM RP tau/theta commutativity smoke over the four edge-family route",
                "diagnostic only; no reflection-positivity theorem, no OS/Wightman theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_reflection_positivity_action_split",
            path=script("ym_reflection_positivity_action_split_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_reflection_positivity_action_split_out),
                "--json",
            ),
            expected_json_path=ym_reflection_positivity_action_split_out,
            optional=True,
            skip_reason=None
            if script("ym_reflection_positivity_action_split_harness.py").exists()
            else "YM RP action-split harness not found",
            notes=(
                "optional exact YM RP action-splitting smoke with S+ / S0 / S- bookkeeping",
                "diagnostic only; no reflection-positivity theorem, no OS/Wightman theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_reflection_positivity_transfer_matrix_hermitian",
            path=script("ym_reflection_positivity_transfer_matrix_hermitian_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_reflection_positivity_transfer_matrix_hermitian_out),
                "--json",
            ),
            expected_json_path=ym_reflection_positivity_transfer_matrix_hermitian_out,
            optional=True,
            skip_reason=None
            if script("ym_reflection_positivity_transfer_matrix_hermitian_harness.py").exists()
            else "YM RP transfer-matrix Hermitian harness not found",
            notes=(
                "optional exact YM RP boundary-preservation and theta-Hermitian transfer-matrix smoke",
                "diagnostic only; no reflection-positivity theorem, no OS/Wightman theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_reflection_positivity_os_axiom",
            path=script("ym_reflection_positivity_os_axiom_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_reflection_positivity_os_axiom_out),
                "--json",
            ),
            expected_json_path=ym_reflection_positivity_os_axiom_out,
            optional=True,
            skip_reason=None
            if script("ym_reflection_positivity_os_axiom_harness.py").exists()
            else "YM RP OS-axiom harness not found",
            notes=(
                "optional exact YM RP OS-axiom modulus-squared structural smoke",
                "diagnostic only; no reflection-positivity theorem, no OS/Wightman theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_reflection_positivity_full_theorem_assembly",
            path=script("ym_reflection_positivity_full_theorem_assembly_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_reflection_positivity_full_theorem_assembly_out),
                "--json",
            ),
            expected_json_path=ym_reflection_positivity_full_theorem_assembly_out,
            optional=True,
            skip_reason=None
            if script("ym_reflection_positivity_full_theorem_assembly_harness.py").exists()
            else "YM RP full-theorem assembly harness not found",
            notes=(
                "optional assembled YM reflection-positivity theorem-route smoke",
                "diagnostic only; no reflection-positivity theorem, no OS/Wightman theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_only_remaining_authority_blockers",
            path=script("ym_only_remaining_authority_blockers_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_only_remaining_authority_blockers_out),
                "--json",
            ),
            expected_json_path=ym_only_remaining_authority_blockers_out,
            optional=True,
            skip_reason=None
            if script("ym_only_remaining_authority_blockers_harness.py").exists()
            else "YM remaining-authority-blockers harness not found",
            notes=(
                "optional authority-only YM blocker ledger smoke",
                "diagnostic only; no external acceptance theorem, no final authority theorem, and no Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ym_standard_language_writeup_readiness",
            path=script("ym_standard_language_writeup_readiness_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_standard_language_writeup_readiness_out),
                "--json",
            ),
            expected_json_path=ym_standard_language_writeup_readiness_out,
            optional=True,
            skip_reason=None
            if script("ym_standard_language_writeup_readiness_harness.py").exists()
            else "YM standard-language writeup readiness harness not found",
            notes=(
                "optional YM writeup/authority readiness ledger smoke",
                "diagnostic only; no theorem publication, no Clay promotion, and no terminal promotion",
            ),
        ),
        HarnessSpec(
            name="ym_standard_language_paper_assembly",
            path=script("ym_standard_language_paper_assembly_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_standard_language_paper_assembly_out),
                "--json",
            ),
            expected_json_path=ym_standard_language_paper_assembly_out,
            optional=True,
            skip_reason=None
            if script("ym_standard_language_paper_assembly_harness.py").exists()
            else "YM standard-language paper assembly harness not found",
            notes=(
                "optional YM standard-language paper assembly ledger smoke",
                "diagnostic only; no paper completion, no Clay promotion, and no terminal promotion",
            ),
        ),
        HarnessSpec(
            name="ym_paper_submission_packet",
            path=script("ym_paper_submission_packet_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ym_paper_submission_packet_out),
                "--json",
            ),
            expected_json_path=ym_paper_submission_packet_out,
            optional=True,
            skip_reason=None
            if script("ym_paper_submission_packet_harness.py").exists()
            else "YM paper submission packet harness not found",
            notes=(
                "optional YM submission-packet ledger smoke",
                "diagnostic only; no submission completion, no Clay promotion, and no terminal promotion",
            ),
        ),
        HarnessSpec(
            name="defect_four_point",
            path=script("defect_four_point_harness.py"),
            args=("--dim", "4", "--samples", "512", "--json", str(defect_four_point_out)),
            expected_json_path=defect_four_point_out,
            notes=("unification four-point residual smoke",),
        ),
        HarnessSpec(
            name="defect_hierarchy_hypothesis_search",
            path=script("defect_hierarchy_hypothesis_search.py"),
            args=(
                "--dim",
                "4",
                "--samples",
                "512",
                "--seed",
                "20260608",
                "--json",
                str(defect_hierarchy_out),
            ),
            expected_json_path=defect_hierarchy_out,
            notes=("unification hierarchy hypothesis separator smoke",),
        ),
        HarnessSpec(
            name="gluing_operator_linearity_proxy",
            path=script("gluing_operator_linearity_proxy_harness.py"),
            args=(
                "--ambient-dim",
                "6",
                "--quotient-dim",
                "4",
                "--samples",
                "256",
                "--seed",
                "20260608",
                "--json-output",
                str(gluing_linearity_out),
                "--json",
            ),
            expected_json_path=gluing_linearity_out,
            notes=(
                "unification quotient-linearity proxy with nonlinear counterexample",
                "diagnostic only; no admissible quotient theorem or unification promotion",
            ),
        ),
        HarnessSpec(
            name="unification_gluing_quotient_admissibility_proxy",
            path=script("unification_gluing_quotient_admissibility_proxy_harness.py"),
            args=(
                "--ambient-dim",
                "7",
                "--quotient-dim",
                "4",
                "--output-dim",
                "4",
                "--radius",
                "3",
                "--json-output",
                str(gluing_quotient_admissibility_out),
                "--json",
            ),
            expected_json_path=gluing_quotient_admissibility_out,
            optional=True,
            skip_reason=None
            if script("unification_gluing_quotient_admissibility_proxy_harness.py").exists()
            else "unification gluing quotient admissibility proxy harness not found",
            notes=(
                "unification quotient-admissibility proxy with representative-leak, nonlinear, and norm-like counterexamples",
                "diagnostic only; no admissible quotient theorem, four-point theorem, or unification promotion",
            ),
        ),
        HarnessSpec(
            name="unification_modulo_null_linearity",
            path=script("unification_modulo_null_linearity_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(unification_modulo_null_linearity_out),
                "--json",
            ),
            expected_json_path=unification_modulo_null_linearity_out,
            optional=True,
            skip_reason=None
            if script("unification_modulo_null_linearity_harness.py").exists()
            else "unification modulo-null linearity harness not found",
            notes=(
                "optional U-1a quotient/null-class smoke for representative invariance, null transport, quotient equality, and modulo-null linearity",
                "diagnostic only; no admissible quotient theorem, four-point theorem, or unification promotion",
            ),
        ),
        HarnessSpec(
            name="unification_cross_term_nullity_theorem",
            path=script("unification_cross_term_nullity_theorem_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(unification_cross_term_nullity_theorem_out),
                "--json",
            ),
            expected_json_path=unification_cross_term_nullity_theorem_out,
            optional=True,
            skip_reason=None
            if script("unification_cross_term_nullity_theorem_harness.py").exists()
            else "Unification cross-term nullity theorem harness not found",
            notes=(
                "optional lightweight theorem-content smoke for the standalone U-1a receipt",
                "diagnostic only; no cross-term theorem, no four-point law, no parallelogram, no quadratic emergence, no terminal promotion",
            ),
        ),
        HarnessSpec(
            name="unification_null_class_stability_theorem",
            path=script("unification_null_class_stability_theorem_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(unification_null_class_stability_theorem_out),
                "--json",
            ),
            expected_json_path=unification_null_class_stability_theorem_out,
            optional=True,
            skip_reason=None
            if script("unification_null_class_stability_theorem_harness.py").exists()
            else "unification null-class stability theorem harness not found",
            notes=(
                "optional lightweight U-1a child smoke for additive/negation closure and representative invariance of the null class",
                "diagnostic only; no admissible quotient theorem, four-point theorem, or unification promotion",
            ),
        ),
        HarnessSpec(
            name="unification_null_transport_modulo_null_consumer",
            path=script("unification_null_transport_modulo_null_consumer_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(unification_null_transport_modulo_null_consumer_out),
                "--json",
            ),
            expected_json_path=unification_null_transport_modulo_null_consumer_out,
            optional=True,
            skip_reason=None
            if script("unification_null_transport_modulo_null_consumer_harness.py").exists()
            else "unification null-transport modulo-null consumer harness not found",
            notes=(
                "optional lightweight U-1a consumer smoke for quotient transport and modulo-null linearity routing into four-point inputs",
                "diagnostic only; no four-point theorem, parallelogram, or unification promotion",
            ),
        ),
        HarnessSpec(
            name="unification_cross_term_child_composite",
            path=script("unification_cross_term_child_composite_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(unification_cross_term_child_composite_out),
                "--json",
            ),
            expected_json_path=unification_cross_term_child_composite_out,
            optional=True,
            skip_reason=None
            if script("unification_cross_term_child_composite_harness.py").exists()
            else "unification cross-term child composite harness not found",
            notes=(
                "optional lightweight U-1a composite smoke joining null-class stability and null-transport consumer routes",
                "diagnostic only; no four-point theorem, parallelogram, or unification promotion",
            ),
        ),
        HarnessSpec(
            name="unification_hc_composite",
            path=script("unification_hc_composite_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(unification_hc_composite_out),
                "--json",
            ),
            expected_json_path=unification_hc_composite_out,
            optional=True,
            skip_reason=None
            if script("unification_hc_composite_harness.py").exists()
            else "unification HC composite harness not found",
            notes=(
                "optional lightweight unification composite smoke from HC into modulo-null linearity and four-point input routing",
                "diagnostic only; no four-point theorem, parallelogram, or unification promotion",
            ),
        ),
        HarnessSpec(
            name="unification_modulo_null_four_point_route",
            path=script("unification_modulo_null_four_point_route_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(unification_modulo_null_four_point_route_out),
                "--json",
            ),
            expected_json_path=unification_modulo_null_four_point_route_out,
            optional=True,
            skip_reason=None
            if script("unification_modulo_null_four_point_route_harness.py").exists()
            else "unification modulo-null/four-point route harness not found",
            notes=(
                "optional lightweight unification route smoke from HC through modulo-null linearity into the four-point cancellation socket",
                "diagnostic only; no four-point theorem, parallelogram theorem, or unification promotion",
            ),
        ),
        HarnessSpec(
            name="unification_parallelogram_jvn_route",
            path=script("unification_parallelogram_jvn_route_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(unification_parallelogram_jvn_route_out),
                "--json",
            ),
            expected_json_path=unification_parallelogram_jvn_route_out,
            optional=True,
            skip_reason=None
            if script("unification_parallelogram_jvn_route_harness.py").exists()
            else "unification parallelogram/Jordan-von-Neumann route harness not found",
            notes=(
                "optional lightweight unification route smoke from four-point routing into parallelogram and Jordan-von-Neumann sockets",
                "diagnostic only; no parallelogram theorem, no Jordan-von-Neumann theorem, and no unification promotion",
            ),
        ),
        HarnessSpec(
            name="unification_discriminant_cross_term",
            path=script("unification_discriminant_cross_term_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(unification_discriminant_cross_term_out),
                "--json",
            ),
            expected_json_path=unification_discriminant_cross_term_out,
            optional=True,
            skip_reason=None
            if script("unification_discriminant_cross_term_harness.py").exists()
            else "Unification discriminant cross-term harness not found",
            notes=(
                "optional discriminant/Cauchy-Schwarz/null-orthogonality smoke for U-1a.2",
                "diagnostic only; no actual cross-term theorem, no quotient-linearity theorem, and no unification promotion",
            ),
        ),
        HarnessSpec(
            name="unification_null_class_subspace",
            path=script("unification_null_class_subspace_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(unification_null_class_subspace_out),
                "--json",
            ),
            expected_json_path=unification_null_class_subspace_out,
            optional=True,
            skip_reason=None
            if script("unification_null_class_subspace_harness.py").exists()
            else "Unification null-class subspace harness not found",
            notes=(
                "optional null-class closure and representative-independence smoke",
                "diagnostic only; no modulo-null linearity theorem, no four-point theorem, and no unification promotion",
            ),
        ),
        HarnessSpec(
            name="unification_parallelogram_from_bilinear",
            path=script("unification_parallelogram_from_bilinear_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(unification_parallelogram_from_bilinear_out),
                "--json",
            ),
            expected_json_path=unification_parallelogram_from_bilinear_out,
            optional=True,
            skip_reason=None
            if script("unification_parallelogram_from_bilinear_harness.py").exists()
            else "Unification parallelogram-from-bilinear harness not found",
            notes=(
                "optional exact parallelogram-from-bilinear/Jordan-von-Neumann route smoke",
                "diagnostic only; no JvN theorem, no signature/Clifford theorem, and no terminal promotion",
            ),
        ),
        HarnessSpec(
            name="unification_u1ah_ns_lane",
            path=script("unification_u1ah_ns_lane_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(unification_u1ah_ns_lane_out),
                "--json",
            ),
            expected_json_path=unification_u1ah_ns_lane_out,
            optional=True,
            skip_reason=None
            if script("unification_u1ah_ns_lane_harness.py").exists()
            else "Unification U-1a-H NS-lane harness not found",
            notes=(
                "optional NS-lane U-1a-H justification smoke using the H10 norm-square route",
                "diagnostic only; no NS authority theorem, no unification promotion, and no terminal promotion",
            ),
        ),
        HarnessSpec(
            name="unification_u1ah_ym_lane",
            path=script("unification_u1ah_ym_lane_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(unification_u1ah_ym_lane_out),
                "--json",
            ),
            expected_json_path=unification_u1ah_ym_lane_out,
            optional=True,
            skip_reason=None
            if script("unification_u1ah_ym_lane_harness.py").exists()
            else "Unification U-1a-H YM-lane harness not found",
            notes=(
                "optional YM-lane U-1a-H justification smoke using vacuum linearization plus cubic remainder budget",
                "diagnostic only; no continuum gauge authority theorem, no unification promotion, and no terminal promotion",
            ),
        ),
        HarnessSpec(
            name="unification_u1ah_global_lane",
            path=script("unification_u1ah_global_lane_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(unification_u1ah_global_lane_out),
                "--json",
            ),
            expected_json_path=unification_u1ah_global_lane_out,
            optional=True,
            skip_reason=None
            if script("unification_u1ah_global_lane_harness.py").exists()
            else "Unification U-1a-H global-lane harness not found",
            notes=(
                "optional global Hilbert-lane U-1a-H justification smoke",
                "diagnostic only; no signature theorem, no Clifford theorem, and no terminal promotion",
            ),
        ),
        HarnessSpec(
            name="unification_clifford_signature_table",
            path=script("unification_clifford_signature_table_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(unification_clifford_signature_table_out),
                "--json",
            ),
            expected_json_path=unification_clifford_signature_table_out,
            optional=True,
            skip_reason=None
            if script("unification_clifford_signature_table_harness.py").exists()
            else "Unification Clifford/signature table harness not found",
            notes=(
                "optional Clifford/signature table smoke for the Dirac/Majorana consumer rows",
                "diagnostic only; no signature theorem, no Clifford theorem, and no terminal promotion",
            ),
        ),
        HarnessSpec(
            name="unification_u1ah_per_lane_composite",
            path=script("unification_u1ah_per_lane_composite_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(unification_u1ah_per_lane_composite_out),
                "--json",
            ),
            expected_json_path=unification_u1ah_per_lane_composite_out,
            optional=True,
            skip_reason=None
            if script("unification_u1ah_per_lane_composite_harness.py").exists()
            else "Unification U-1a-H per-lane composite harness not found",
            notes=(
                "optional assembled U-1a-H per-lane justification smoke",
                "diagnostic only; no unification theorem, no signature/Clifford theorem, and no terminal promotion",
            ),
        ),
        HarnessSpec(
            name="unification_signature_clifford_consumer_socket",
            path=script("unification_signature_clifford_consumer_socket_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(unification_signature_clifford_consumer_socket_out),
                "--json",
            ),
            expected_json_path=unification_signature_clifford_consumer_socket_out,
            optional=True,
            skip_reason=None
            if script("unification_signature_clifford_consumer_socket_harness.py").exists()
            else "Unification signature/Clifford consumer socket harness not found",
            notes=(
                "optional signature/Clifford consumer socket smoke above the JvN route",
                "diagnostic only; no signature theorem, no Clifford theorem, and no terminal promotion",
            ),
        ),
        HarnessSpec(
            name="unification_lane_justification_authority",
            path=script("unification_lane_justification_authority_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(unification_lane_justification_authority_out),
                "--json",
            ),
            expected_json_path=unification_lane_justification_authority_out,
            optional=True,
            skip_reason=None
            if script("unification_lane_justification_authority_harness.py").exists()
            else "Unification lane-justification authority harness not found",
            notes=(
                "optional unification lane-justification and authority-gap ledger smoke",
                "diagnostic only; no final signature theorem, no final Clifford theorem, and no terminal promotion",
            ),
        ),
        HarnessSpec(
            name="unification_consumer_authority_assembly",
            path=script("unification_consumer_authority_assembly_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(unification_consumer_authority_assembly_out),
                "--json",
            ),
            expected_json_path=unification_consumer_authority_assembly_out,
            optional=True,
            skip_reason=None
            if script("unification_consumer_authority_assembly_harness.py").exists()
            else "Unification consumer-authority assembly harness not found",
            notes=(
                "optional unification consumer-authority assembly ledger smoke",
                "diagnostic only; no final consumer authority theorem and no terminal promotion",
            ),
        ),
        HarnessSpec(
            name="unification_authority_review_packet",
            path=script("unification_authority_review_packet_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(unification_authority_review_packet_out),
                "--json",
            ),
            expected_json_path=unification_authority_review_packet_out,
            optional=True,
            skip_reason=None
            if script("unification_authority_review_packet_harness.py").exists()
            else "Unification authority-review packet harness not found",
            notes=(
                "optional unification review-packet ledger smoke",
                "diagnostic only; no review completion and no terminal promotion",
            ),
        ),
        HarnessSpec(
            name="ns_writeup_and_constants_readiness",
            path=script("ns_writeup_and_constants_readiness_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ns_writeup_and_constants_readiness_out),
                "--json",
            ),
            expected_json_path=ns_writeup_and_constants_readiness_out,
            optional=True,
            skip_reason=None
            if script("ns_writeup_and_constants_readiness_harness.py").exists()
            else "NS writeup/constants readiness harness not found",
            notes=(
                "optional NS writeup/constants/PDE-translation readiness ledger smoke",
                "diagnostic only; no theorem writeup completion, no Clay promotion, and no terminal promotion",
            ),
        ),
        HarnessSpec(
            name="ns_standard_pde_writeup_assembly",
            path=script("ns_standard_pde_writeup_assembly_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ns_standard_pde_writeup_assembly_out),
                "--json",
            ),
            expected_json_path=ns_standard_pde_writeup_assembly_out,
            optional=True,
            skip_reason=None
            if script("ns_standard_pde_writeup_assembly_harness.py").exists()
            else "NS standard PDE writeup assembly harness not found",
            notes=(
                "optional NS standard-PDE paper assembly ledger smoke",
                "diagnostic only; no paper completion, no Clay promotion, and no terminal promotion",
            ),
        ),
        HarnessSpec(
            name="ns_paper_submission_packet",
            path=script("ns_paper_submission_packet_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(ns_paper_submission_packet_out),
                "--json",
            ),
            expected_json_path=ns_paper_submission_packet_out,
            optional=True,
            skip_reason=None
            if script("ns_paper_submission_packet_harness.py").exists()
            else "NS paper submission packet harness not found",
            notes=(
                "optional NS submission-packet ledger smoke",
                "diagnostic only; no submission completion, no Clay promotion, and no terminal promotion",
            ),
        ),
        HarnessSpec(
            name="ns_boundary_component_lambda3_diagnostic",
            path=script("ns_boundary_component_lambda3_diagnostic.py"),
            args=(
                "--input",
                str(ns_boundary_smoke_derived_input),
                "--lambda2-band",
                "1e-6",
                "--json",
                "--output",
                str(ns_boundary_component_lambda3_out),
            )
            if ns_boundary_smoke_derived_input is not None
            else ("--json",),
            expected_json_path=ns_boundary_component_lambda3_out,
            optional=True,
            skip_reason=None
            if ns_boundary_smoke_derived_input is not None and script("ns_boundary_component_lambda3_diagnostic.py").exists()
            else (
                "ns_boundary_component_lambda3_diagnostic harness not found"
                if not script("ns_boundary_component_lambda3_diagnostic.py").exists()
                else "ns_boundary_component_lambda3_diagnostic requires a discoverable derived NS boundary archive under /tmp"
            ),
            notes=(
                "boundary component lambda3 diagnostics over connected boundary components",
                "empirical/non-promoting; no lambda3 boundary theorem promotion",
            ),
        ),
        HarnessSpec(
            name="ns_boundary_f123_absorption_diagnostic",
            path=script("ns_boundary_f123_absorption_diagnostic.py"),
            args=(
                "--input",
                str(ns_boundary_smoke_derived_input),
                "--json",
                "--output",
                str(ns_boundary_f123_absorption_out),
            )
            if ns_boundary_smoke_derived_input is not None
            else ("--json",),
            expected_json_path=ns_boundary_f123_absorption_out,
            optional=True,
            skip_reason=None
            if ns_boundary_smoke_derived_input is not None and script("ns_boundary_f123_absorption_diagnostic.py").exists()
            else (
                "ns_boundary_f123_absorption_diagnostic harness not found"
                if not script("ns_boundary_f123_absorption_diagnostic.py").exists()
                else "ns_boundary_f123_absorption_diagnostic requires a discoverable derived NS boundary archive under /tmp"
            ),
            notes=(
                "boundary f123 absorption diagnostics for near-singular component structure",
                "empirical/non-promoting; no absorption theorem promotion",
            ),
        ),
        HarnessSpec(
            name="ns_boundary_corrected_gronwall_margin",
            path=script("ns_boundary_component_lambda3_corrected_gronwall_margin.py"),
            args=(
                "--lambda3-json",
                str(ns_boundary_component_lambda3_out),
                "--output",
                str(ns_boundary_corrected_gronwall_margin_out),
            )
            + (
                (
                    "--f123-json",
                    str(ns_boundary_f123_absorption_out),
                )
                if ns_boundary_f123_absorption_out.exists()
                else ()
            )
            if ns_boundary_smoke_derived_input is not None
            else ("--help",),
            expected_json_path=ns_boundary_corrected_gronwall_margin_out,
            optional=True,
            skip_reason=None
            if ns_boundary_smoke_derived_input is not None
            and script("ns_boundary_component_lambda3_corrected_gronwall_margin.py").exists()
            else (
                "ns_boundary_corrected_gronwall_margin script not found"
                if not script("ns_boundary_component_lambda3_corrected_gronwall_margin.py").exists()
                else "ns_boundary_corrected_gronwall_margin requires derived NS boundary lambda3/f123 diagnostics under /tmp"
            ),
            notes=(
                "optional corrected Gronwall margin diagnostic over boundary lambda3/F123 outputs",
                "empirical/conditional/non-promoting; does not discharge h_delta1 or Clay NS",
            ),
        ),
        HarnessSpec(
            name="ns_boundary_timeseries_margin_summary",
            path=script("ns_boundary_timeseries_margin_summary.py"),
            args=(
                "--inputs",
                str(ns_boundary_corrected_gronwall_margin_out),
                "--output",
                str(ns_boundary_timeseries_margin_summary_out),
            ),
            expected_json_path=ns_boundary_timeseries_margin_summary_out,
            optional=True,
            skip_reason=None
            if ns_boundary_corrected_gronwall_margin_out.exists()
            and script("ns_boundary_timeseries_margin_summary.py").exists()
            else (
                "ns_boundary_timeseries_margin_summary script not found"
                if not script("ns_boundary_timeseries_margin_summary.py").exists()
                else "ns_boundary_timeseries_margin_summary requires corrected-gronwall-margin artifact"
            ),
            notes=(
                "optional aggregate corrected-gronwall timeseries summary from margin diagnostics",
                "empirical/conditional/non-promoting; does not discharge h_delta1 or Clay NS",
            ),
        ),
        HarnessSpec(
            name="check_ns_boundary_gronwall_margin_regression",
            path=script("check_ns_boundary_gronwall_margin_regression.py"),
            args=(
                "--margin-json",
                str(ns_boundary_corrected_gronwall_margin_out),
            )
            + (
                (
                    "--timeseries-json",
                    str(ns_boundary_timeseries_margin_summary_out),
                )
                if ns_boundary_timeseries_margin_summary_out.exists()
                else ()
            )
            if ns_boundary_timeseries_margin_summary_out.exists()
            or ns_boundary_corrected_gronwall_margin_out.exists()
            else ("--help",),
            expected_json_path=ns_boundary_gronwall_margin_regression_out,
            optional=True,
            skip_reason=None
            if ns_boundary_corrected_gronwall_margin_out.exists()
            and script("check_ns_boundary_gronwall_margin_regression.py").exists()
            else (
                "check_ns_boundary_gronwall_margin_regression script not found"
                if not script("check_ns_boundary_gronwall_margin_regression.py").exists()
                else "check_ns_boundary_gronwall_margin_regression requires corrected-gronwall margin artifact"
            ),
            notes=(
                "optional regression check for corrected Gronwall margin invariants and optional timeseries summary",
                "empirical/conditional/non-promoting; does not discharge h_delta1 or Clay NS",
            ),
        ),
        HarnessSpec(
            name="ns_boundary_theoremg_cancellation_margin",
            path=script("ns_boundary_theoremg_cancellation_margin.py"),
            args=(
                "--margin-json",
                str(ns_boundary_corrected_gronwall_margin_out),
                "--output-json",
                str(ns_boundary_theoremg_cancellation_margin_out),
            )
            if ns_boundary_corrected_gronwall_margin_out.exists()
            else ("--help",),
            expected_json_path=ns_boundary_theoremg_cancellation_margin_out,
            optional=True,
            skip_reason=None
            if ns_boundary_corrected_gronwall_margin_out.exists()
            and script("ns_boundary_theoremg_cancellation_margin.py").exists()
            else (
                "ns_boundary_theoremg_cancellation_margin script not found"
                if not script("ns_boundary_theoremg_cancellation_margin.py").exists()
                else "ns_boundary_theoremg_cancellation_margin requires corrected-gronwall margin artifact"
            ),
            notes=(
                "optional Theorem-G cancellation-margin upgrade from corrected Gronwall margin artifact",
                "empirical/non-promoting; records mu_cancellation=delta1 and does not prove Clay NS",
            ),
        ),
        HarnessSpec(
            name="check_ns_boundary_cancellation_margin_regression",
            path=script("check_ns_boundary_cancellation_margin_regression.py"),
            args=(
                "--cancellation-json",
                str(ns_boundary_theoremg_cancellation_margin_out),
            )
            if ns_boundary_theoremg_cancellation_margin_out.exists()
            else ("--help",),
            expected_json_path=ns_boundary_cancellation_margin_regression_out,
            optional=True,
            skip_reason=None
            if ns_boundary_theoremg_cancellation_margin_out.exists()
            and script("check_ns_boundary_cancellation_margin_regression.py").exists()
            else (
                "check_ns_boundary_cancellation_margin_regression script not found"
                if not script("check_ns_boundary_cancellation_margin_regression.py").exists()
                else "check_ns_boundary_cancellation_margin_regression requires cancellation-margin artifact"
            ),
            notes=(
                "optional regression check for cancellation-margin invariants",
                "regression-only/non-promoting; no theorem or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_boundary_pressure_poisson_bypass_diagnostic",
            path=script("ns_boundary_pressure_poisson_bypass_diagnostic.py"),
            args=(
                "--derived-archive",
                str(ns_boundary_smoke_derived_input),
                "--lambda2-band",
                "1e-6",
                "--output-json",
                str(ns_boundary_pressure_poisson_bypass_out),
            )
            if ns_boundary_smoke_derived_input is not None
            else ("--help",),
            expected_json_path=ns_boundary_pressure_poisson_bypass_out,
            optional=True,
            skip_reason=None
            if ns_boundary_smoke_derived_input is not None
            and script("ns_boundary_pressure_poisson_bypass_diagnostic.py").exists()
            else (
                "ns_boundary_pressure_poisson_bypass_diagnostic script not found"
                if not script("ns_boundary_pressure_poisson_bypass_diagnostic.py").exists()
                else "ns_boundary_pressure_poisson_bypass_diagnostic requires a discoverable derived NS boundary archive under /tmp"
            ),
            notes=(
                "optional pressure-Poisson bypass diagnostic over boundary components",
                "empirical/non-promoting; does not prove layer CZ, geometric concentration, or Clay NS",
            ),
        ),
        HarnessSpec(
            name="ns_boundary_geometric_concentration_diagnostic",
            path=script("ns_boundary_geometric_concentration_diagnostic.py"),
            args=(
                "--derived-archive",
                str(ns_boundary_smoke_derived_input),
                "--lambda2-band",
                "1e-6",
                "--output-json",
                str(ns_boundary_geometric_concentration_out),
            )
            if ns_boundary_smoke_derived_input is not None
            else ("--help",),
            expected_json_path=ns_boundary_geometric_concentration_out,
            optional=True,
            skip_reason=None
            if ns_boundary_smoke_derived_input is not None
            and script("ns_boundary_geometric_concentration_diagnostic.py").exists()
            else (
                "ns_boundary_geometric_concentration_diagnostic script not found"
                if not script("ns_boundary_geometric_concentration_diagnostic.py").exists()
                else "ns_boundary_geometric_concentration_diagnostic requires a discoverable derived NS boundary archive under /tmp"
            ),
            notes=(
                "optional geometric concentration diagnostic for top-vorticity alignment with Kato carrier",
                "empirical/non-promoting; does not prove blow-up carrier concentration or Clay NS",
            ),
        ),
        HarnessSpec(
            name="check_ns_boundary_pressure_geometric_regression",
            path=script("check_ns_boundary_pressure_geometric_regression.py"),
            args=(
                (
                    "--pressure-json",
                    str(ns_boundary_pressure_poisson_bypass_out),
                )
                if ns_boundary_pressure_poisson_bypass_out.exists()
                else ()
            )
            + (
                (
                    "--geometric-json",
                    str(ns_boundary_geometric_concentration_out),
                )
                if ns_boundary_geometric_concentration_out.exists()
                else ()
            )
            if ns_boundary_pressure_poisson_bypass_out.exists()
            or ns_boundary_geometric_concentration_out.exists()
            else ("--help",),
            expected_json_path=ns_boundary_pressure_geometric_regression_out,
            optional=True,
            skip_reason=None
            if (
                ns_boundary_pressure_poisson_bypass_out.exists()
                or ns_boundary_geometric_concentration_out.exists()
            )
            and script("check_ns_boundary_pressure_geometric_regression.py").exists()
            else (
                "check_ns_boundary_pressure_geometric_regression script not found"
                if not script("check_ns_boundary_pressure_geometric_regression.py").exists()
                else "check_ns_boundary_pressure_geometric_regression requires pressure/geometric diagnostic artifacts"
            ),
            notes=(
                "optional regression check for pressure-bypass and geometric-concentration diagnostic invariants",
                "regression-only/non-promoting; no theorem or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_boundary_g12_bounds_diagnostic",
            path=script("ns_boundary_g12_bounds_diagnostic.py"),
            args=(
                "--derived-archive",
                str(ns_boundary_smoke_derived_input),
                "--lambda2-band",
                "1e-6",
                "--output-json",
                str(ns_boundary_g12_bounds_out),
            )
            if ns_boundary_smoke_derived_input is not None
            else ("--help",),
            expected_json_path=ns_boundary_g12_bounds_out,
            optional=True,
            skip_reason=None
            if ns_boundary_smoke_derived_input is not None
            and script("ns_boundary_g12_bounds_diagnostic.py").exists()
            else (
                "ns_boundary_g12_bounds_diagnostic script not found"
                if not script("ns_boundary_g12_bounds_diagnostic.py").exists()
                else "ns_boundary_g12_bounds_diagnostic requires a discoverable derived NS boundary archive under /tmp"
            ),
            notes=(
                "optional g12 lower/upper bound telemetry over global, boundary-carrier, and beta regions",
                "empirical/non-promoting; does not prove GD1 upper-bound or Clay NS",
            ),
        ),
        HarnessSpec(
            name="ns_interior_vorticity_budget_diagnostic",
            path=script("ns_interior_vorticity_budget_diagnostic.py"),
            args=(
                "--input",
                str(ns_raw_pressure_smoke_input),
                "--frame",
                "0",
                "--output-json",
                str(ns_interior_vorticity_budget_out),
            )
            if ns_raw_pressure_smoke_input is not None
            else ("--help",),
            expected_json_path=ns_interior_vorticity_budget_out,
            optional=True,
            skip_reason=None
            if ns_raw_pressure_smoke_input is not None
            and script("ns_interior_vorticity_budget_diagnostic.py").exists()
            else (
                "ns_interior_vorticity_budget_diagnostic script not found"
                if not script("ns_interior_vorticity_budget_diagnostic.py").exists()
                else "ns_interior_vorticity_budget_diagnostic requires a raw NS pressure archive under /tmp"
            ),
            notes=(
                "optional Calc-6 interior pointwise vorticity budget diagnostic",
                "empirical/non-promoting; does not prove the interior maximum principle or Clay NS",
            ),
        ),
        HarnessSpec(
            name="ns_omega_l3_timeseries_diagnostic",
            path=script("ns_omega_l3_timeseries_diagnostic.py"),
            args=(
                "--input",
                str(ns_raw_pressure_smoke_input),
                "--output-json",
                str(ns_omega_l3_timeseries_out),
            )
            if ns_raw_pressure_smoke_input is not None
            else ("--help",),
            expected_json_path=ns_omega_l3_timeseries_out,
            optional=True,
            skip_reason=None
            if ns_raw_pressure_smoke_input is not None
            and script("ns_omega_l3_timeseries_diagnostic.py").exists()
            else (
                "ns_omega_l3_timeseries_diagnostic script not found"
                if not script("ns_omega_l3_timeseries_diagnostic.py").exists()
                else "ns_omega_l3_timeseries_diagnostic requires a raw NS pressure archive under /tmp"
            ),
            notes=(
                "optional Calc-7 omega L3 timeseries diagnostic",
                "empirical/non-promoting; does not prove enstrophy Gronwall closure or Clay NS",
            ),
        ),
        HarnessSpec(
            name="ns_layer_l2_vorticity_fraction",
            path=script("ns_layer_l2_vorticity_fraction_diagnostic.py"),
            args=(
                "--raw-archive",
                str(ns_raw_pressure_smoke_input),
                "--derived-archive",
                "/tmp/ns_boundary_true_korn_timeseries_N128_20260618",
                "--output-json",
                str(ns_layer_l2_vorticity_fraction_out),
            )
            if ns_raw_pressure_smoke_input is not None
            and Path("/tmp/ns_boundary_true_korn_timeseries_N128_20260618").exists()
            else ("--help",),
            expected_json_path=ns_layer_l2_vorticity_fraction_out,
            optional=True,
            skip_reason=None
            if ns_raw_pressure_smoke_input is not None
            and Path("/tmp/ns_boundary_true_korn_timeseries_N128_20260618").exists()
            and script("ns_layer_l2_vorticity_fraction_diagnostic.py").exists()
            else (
                "ns_layer_l2_vorticity_fraction_diagnostic script not found"
                if not script("ns_layer_l2_vorticity_fraction_diagnostic.py").exists()
                else "ns_layer_l2_vorticity_fraction requires raw archive and derived frame directory"
            ),
            notes=(
                "optional Calc-8 layer-L2 vorticity fraction diagnostic",
                "empirical/non-promoting; does not prove SerrinFromQ2Control or Clay NS",
            ),
        ),
        HarnessSpec(
            name="ns_layer_l2_vorticity_fraction_summary",
            path=script("ns_layer_l2_vorticity_fraction_summary.py"),
            args=(
                str(ns_layer_l2_vorticity_fraction_out),
                "--output",
                str(ns_layer_l2_vorticity_fraction_summary_out),
            )
            if ns_layer_l2_vorticity_fraction_out.exists()
            else ("--help",),
            expected_json_path=ns_layer_l2_vorticity_fraction_summary_out,
            optional=True,
            skip_reason=None
            if ns_layer_l2_vorticity_fraction_out.exists()
            and script("ns_layer_l2_vorticity_fraction_summary.py").exists()
            else (
                "ns_layer_l2_vorticity_fraction_summary script not found"
                if not script("ns_layer_l2_vorticity_fraction_summary.py").exists()
                else "ns_layer_l2_vorticity_fraction_summary requires the Calc-8 diagnostic output"
            ),
            notes=(
                "optional Calc-8 layer-L2 summary",
                "heuristic Shahmurov/Serrin route telemetry only",
            ),
        ),
        HarnessSpec(
            name="check_ns_layer_l2_vorticity_fraction_regression",
            path=script("check_ns_layer_l2_vorticity_fraction_regression.py"),
            args=(
                str(ns_layer_l2_vorticity_fraction_out),
                "--output-json",
                str(ns_layer_l2_vorticity_fraction_regression_out),
            )
            if ns_layer_l2_vorticity_fraction_out.exists()
            else ("--help",),
            expected_json_path=ns_layer_l2_vorticity_fraction_regression_out,
            optional=True,
            skip_reason=None
            if ns_layer_l2_vorticity_fraction_out.exists()
            and script("check_ns_layer_l2_vorticity_fraction_regression.py").exists()
            else (
                "check_ns_layer_l2_vorticity_fraction_regression script not found"
                if not script("check_ns_layer_l2_vorticity_fraction_regression.py").exists()
                else "check_ns_layer_l2_vorticity_fraction_regression requires the Calc-8 diagnostic output"
            ),
            notes=(
                "optional Calc-8 layer-L2 regression gate",
                "empirical/non-promoting; validates JSON shape only",
            ),
        ),
        HarnessSpec(
            name="ns_pressure_poisson_sign_audit",
            path=script("ns_pressure_poisson_sign_audit.py"),
            args=(
                "--input",
                str(ns_raw_pressure_smoke_input),
                "--frame",
                "0",
                "--output-json",
                str(ns_pressure_poisson_sign_audit_out),
            )
            if ns_raw_pressure_smoke_input is not None
            else ("--help",),
            expected_json_path=ns_pressure_poisson_sign_audit_out,
            optional=True,
            skip_reason=None
            if ns_raw_pressure_smoke_input is not None
            and script("ns_pressure_poisson_sign_audit.py").exists()
            else (
                "ns_pressure_poisson_sign_audit script not found"
                if not script("ns_pressure_poisson_sign_audit.py").exists()
                else "ns_pressure_poisson_sign_audit requires a raw NS pressure archive under /tmp"
            ),
            notes=(
                "optional pressure-Poisson sign/convention audit",
                "empirical/non-promoting; does not prove pressure-CZ closure or Clay NS",
            ),
        ),
        HarnessSpec(
            name="check_ns_interior_pressure_regression",
            path=script("check_ns_interior_pressure_regression.py"),
            args=(
                (
                    "--interior-json",
                    str(ns_interior_vorticity_budget_out),
                )
                if ns_interior_vorticity_budget_out.exists()
                else ()
            )
            + (
                (
                    "--l3-json",
                    str(ns_omega_l3_timeseries_out),
                )
                if ns_omega_l3_timeseries_out.exists()
                else ()
            )
            if ns_interior_vorticity_budget_out.exists()
            or ns_omega_l3_timeseries_out.exists()
            else ("--help",),
            expected_json_path=ns_interior_pressure_regression_out,
            optional=True,
            skip_reason=None
            if (
                ns_interior_vorticity_budget_out.exists()
                or ns_omega_l3_timeseries_out.exists()
            )
            and script("check_ns_interior_pressure_regression.py").exists()
            else (
                "check_ns_interior_pressure_regression script not found"
                if not script("check_ns_interior_pressure_regression.py").exists()
                else "check_ns_interior_pressure_regression requires interior or L3 artifacts"
            ),
            notes=(
                "optional regression check for interior budget and omega L3 diagnostics",
                "regression-only/non-promoting; no theorem or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="ns_pressure_poisson_sign_timeseries_audit",
            path=script("ns_pressure_poisson_sign_timeseries_audit.py"),
            args=(
                "--input",
                str(ns_raw_pressure_smoke_input),
                "--frames",
                "0",
                "--output-json",
                str(ns_pressure_poisson_sign_timeseries_out),
            )
            if ns_raw_pressure_smoke_input is not None
            else ("--help",),
            expected_json_path=ns_pressure_poisson_sign_timeseries_out,
            optional=True,
            skip_reason=None
            if ns_raw_pressure_smoke_input is not None
            and script("ns_pressure_poisson_sign_timeseries_audit.py").exists()
            else (
                "ns_pressure_poisson_sign_timeseries_audit script not found"
                if not script("ns_pressure_poisson_sign_timeseries_audit.py").exists()
                else "ns_pressure_poisson_sign_timeseries_audit requires a raw NS pressure archive under /tmp"
            ),
            notes=(
                "optional pressure-Poisson sign timeseries audit",
                "empirical/non-promoting; does not prove pressure convention normalization or Clay NS",
            ),
        ),
        HarnessSpec(
            name="ns_interior_budget_timeseries_diagnostic",
            path=script("ns_interior_budget_timeseries_diagnostic.py"),
            args=(
                "--input",
                str(ns_raw_pressure_smoke_input),
                "--frames",
                "0",
                "--output-json",
                str(ns_interior_budget_timeseries_out),
            )
            if ns_raw_pressure_smoke_input is not None
            else ("--help",),
            expected_json_path=ns_interior_budget_timeseries_out,
            optional=True,
            skip_reason=None
            if ns_raw_pressure_smoke_input is not None
            and script("ns_interior_budget_timeseries_diagnostic.py").exists()
            else (
                "ns_interior_budget_timeseries_diagnostic script not found"
                if not script("ns_interior_budget_timeseries_diagnostic.py").exists()
                else "ns_interior_budget_timeseries_diagnostic requires a raw NS pressure archive under /tmp"
            ),
            notes=(
                "optional interior budget timeseries diagnostic",
                "empirical/non-promoting; does not prove the pressure-mediated maximum principle or Clay NS",
            ),
        ),
        HarnessSpec(
            name="ns_pressure_poisson_bypass_convention_normalized",
            path=script("ns_pressure_poisson_bypass_convention_normalized.py"),
            args=(
                "--derived-archive",
                str(ns_boundary_smoke_derived_input),
                "--lambda2-band",
                "1e-6",
                "--convention",
                "plus",
                "--output-json",
                str(ns_pressure_poisson_bypass_convention_normalized_out),
            )
            if ns_boundary_smoke_derived_input is not None
            else ("--help",),
            expected_json_path=ns_pressure_poisson_bypass_convention_normalized_out,
            optional=True,
            skip_reason=None
            if ns_boundary_smoke_derived_input is not None
            and script("ns_pressure_poisson_bypass_convention_normalized.py").exists()
            else (
                "ns_pressure_poisson_bypass_convention_normalized script not found"
                if not script("ns_pressure_poisson_bypass_convention_normalized.py").exists()
                else "ns_pressure_poisson_bypass_convention_normalized requires a discoverable derived NS archive under /tmp"
            ),
            notes=(
                "optional convention-normalized pressure-bypass diagnostic",
                "empirical/non-promoting; does not prove pressure-Poisson bypass or Clay NS",
            ),
        ),
        HarnessSpec(
            name="check_ns_pressure_convention_regression",
            path=script("check_ns_pressure_convention_regression.py"),
            args=(
                (
                    "--sign-timeseries-json",
                    str(ns_pressure_poisson_sign_timeseries_out),
                )
                if ns_pressure_poisson_sign_timeseries_out.exists()
                else ()
            )
            + (
                (
                    "--budget-timeseries-json",
                    str(ns_interior_budget_timeseries_out),
                )
                if ns_interior_budget_timeseries_out.exists()
                else ()
            )
            if ns_pressure_poisson_sign_timeseries_out.exists()
            or ns_interior_budget_timeseries_out.exists()
            else ("--help",),
            expected_json_path=ns_pressure_convention_regression_out,
            optional=True,
            skip_reason=None
            if (
                ns_pressure_poisson_sign_timeseries_out.exists()
                or ns_interior_budget_timeseries_out.exists()
            )
            and script("check_ns_pressure_convention_regression.py").exists()
            else (
                "check_ns_pressure_convention_regression script not found"
                if not script("check_ns_pressure_convention_regression.py").exists()
                else "check_ns_pressure_convention_regression requires sign or budget convention artifacts"
            ),
            notes=(
                "optional regression check for pressure convention diagnostics",
                "regression-only/non-promoting; no theorem or Clay promotion",
            ),
        ),
        HarnessSpec(
            name="unification_scale_invariant_cross_term",
            path=script("unification_scale_invariant_cross_term_harness.py"),
            args=(
                "--json-output",
                str(unification_scale_invariant_cross_term_out),
                "--json",
            ),
            expected_json_path=unification_scale_invariant_cross_term_out,
            optional=True,
            skip_reason=None
            if script("unification_scale_invariant_cross_term_harness.py").exists()
            else "Unification scale-invariant cross-term harness not found",
            notes=(
                "optional U-1a-H and Jordan-von Neumann route smoke",
                "diagnostic only; no four-point theorem, no quadratic emergence, and no terminal promotion",
            ),
        ),
        HarnessSpec(
            name="unification_quotient_four_point_stress",
            path=script("unification_quotient_four_point_stress_harness.py"),
            args=(
                "--dimension",
                "4",
                "--samples",
                "256",
                "--tolerance",
                "0.000001",
                "--bad-floor",
                "0.01",
                "--json-output",
                str(unification_quotient_four_point_stress_out),
                "--json",
            ),
            expected_json_path=unification_quotient_four_point_stress_out,
            optional=True,
            skip_reason=None
            if script("unification_quotient_four_point_stress_harness.py").exists()
            else "unification quotient four-point stress harness not found",
            notes=(
                "unification four-point residual stress harness with representative-shift, nonlinear, p-norm, and asymmetric-cross-term bad cases",
                "diagnostic only; no quotient admissibility theorem, parallelogram theorem, or unification promotion",
            ),
        ),
        HarnessSpec(
            name="unification_cross_term_to_four_point_pipeline",
            path=script("unification_cross_term_to_four_point_pipeline_harness.py"),
            args=(
                "--quick",
                "--json-output",
                str(unification_cross_term_to_four_point_pipeline_out),
                "--json",
            ),
            expected_json_path=unification_cross_term_to_four_point_pipeline_out,
            optional=True,
            skip_reason=None
            if script("unification_cross_term_to_four_point_pipeline_harness.py").exists()
            else "unification cross-term to four-point pipeline harness not found",
            notes=(
                "optional U-1a pipeline smoke from cross-term nullity through modulo-null linearity into four-point/parallelogram diagnostics",
                "diagnostic only; no cross-term theorem, four-point theorem, or unification promotion",
            ),
        ),
        HarnessSpec(
            name="unification_hierarchy_consistency_kills_four_point_defect",
            path=script("unification_hierarchy_consistency_kills_four_point_defect_harness.py"),
            args=(
                "--json-output",
                str(unification_hierarchy_consistency_kills_four_point_defect_out),
                "--json",
            ),
            expected_json_path=unification_hierarchy_consistency_kills_four_point_defect_out,
            optional=True,
            skip_reason=None
            if script("unification_hierarchy_consistency_kills_four_point_defect_harness.py").exists()
            else "Unification HC->four-point harness not found",
            notes=(
                "optional unification smoke for hierarchy consistency collapsing the four-point defect",
                "diagnostic only; no four-point theorem, no parallelogram theorem, and no unification promotion",
            ),
        ),
    ]

    optional_sign_jacobian_candidates = (
        ("ns_sign_antisymmetry_jacobian_optional", script("ns_sign_antisymmetry_jacobian_harness.py")),
        (
            "ns_exact_sign_antisymmetry_jacobian_optional",
            script("ns_exact_sign_antisymmetry_jacobian_harness.py"),
        ),
        ("ns_jacobian_sign_antisymmetry_optional", script("ns_jacobian_sign_antisymmetry_harness.py")),
    )
    for name, candidate in optional_sign_jacobian_candidates:
        if candidate.exists():
            out = CHILD_OUT_DIR / f"{name}.json"
            specs.append(
                HarnessSpec(
                    name=name,
                    path=candidate,
                    args=("--samples", "128", "--seed", "20260608", "--json-output", str(out)),
                    expected_json_path=out,
                    optional=True,
                    notes=("optional sign/antisymmetry/Jacobian harness discovered at runtime",),
                )
            )

    gray_candidates = [
        REPO_ROOT / "scripts" / "gray_scott_triadic_defect_harness.py",
        REPO_ROOT.parent / "dashifine" / "scripts" / "gray_scott_triadic_defect_harness.py",
        REPO_ROOT.parent / "dashitest" / "scripts" / "gray_scott_triadic_defect_harness.py",
        REPO_ROOT.parent / "dashifine" / "newtest" / "grayscott_krr.py",
        REPO_ROOT.parent / "dashitest" / "newtest" / "grayscott_krr.py",
    ]
    gray_path = next((candidate for candidate in gray_candidates if candidate.exists()), None)
    if gray_path is None:
        specs.append(
            HarnessSpec(
                name="gray_scott_optional",
                path=gray_candidates[0],
                optional=True,
                skip_reason="no Gray-Scott diagnostic harness found in repo, ../dashifine, or ../dashitest",
            )
        )
    elif gray_path.name == "grayscott_krr.py":
        gray_out = CHILD_OUT_DIR / "grayscott_krr_smoke"
        specs.append(
            HarnessSpec(
                name="gray_scott_krr_smoke_optional",
                path=gray_path,
                args=(
                    "--output_dir",
                    str(gray_out),
                    "--grid",
                    "8",
                    "--steps",
                    "12",
                    "--burn_in",
                    "2",
                    "--frames",
                    "3",
                    "--per_frame",
                    "8",
                    "--rollout_steps",
                    "1",
                    "--rollout_snapshot_steps",
                    "",
                    "--rollout_gif_steps",
                    "0",
                    "--seed",
                    "20260608",
                ),
                optional=True,
                notes=(
                    "sibling Gray-Scott KRR smoke only; not a triadic Clay diagnostic",
                ),
            )
        )
    else:
        gray_out = CHILD_OUT_DIR / "gray_scott_triadic_defect_smoke.json"
        specs.append(
            HarnessSpec(
                name="gray_scott_triadic_defect_optional",
                path=gray_path,
                args=(
                    "--json-output",
                    str(gray_out),
                    "--grid",
                    "16",
                    "--steps",
                    "24",
                    "--analysis-frames",
                    "4",
                    "--triads-per-frame",
                    "64",
                    "--max-modes",
                    "32",
                    "--shells",
                    "8",
                    "--angle-bins",
                    "18",
                    "--seed",
                    "20260608",
                ),
                expected_json_path=gray_out,
                optional=True,
                notes=("optional Gray-Scott triadic diagnostic smoke",),
            )
        )

    # Keep the interpreter explicit for manifest readability.
    return [
        HarnessSpec(
            name=spec.name,
            path=spec.path,
            args=(py, str(spec.path), *spec.args),
            expected_json_path=spec.expected_json_path,
            optional=spec.optional,
            skip_reason=spec.skip_reason,
            notes=spec.notes,
        )
        for spec in specs
    ]


def run_spec(spec: HarnessSpec, timeout_seconds: int) -> HarnessResult:
    result = HarnessResult(
        name=spec.name,
        discovered=spec.path.exists(),
        command=list(spec.args),
        skipped=False,
        skip_reason=None,
        notes=list(spec.notes),
    )

    if spec.skip_reason is not None:
        if spec.optional:
            result.skipped = True
            result.skip_reason = spec.skip_reason
        else:
            result.return_code = 127
            result.stderr_tail = spec.skip_reason
            result.notes.append("required harness dependency missing")
        return result

    if not spec.path.exists():
        if spec.optional:
            result.skipped = True
            result.skip_reason = "harness script not found"
        else:
            result.return_code = 127
            result.stderr_tail = f"required harness script not found: {rel(spec.path)}"
            result.notes.append("required harness missing")
        return result

    started = time.monotonic()
    try:
        completed = subprocess.run(
            spec.args,
            cwd=REPO_ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout_seconds,
            check=False,
            env={**os.environ, "PYTHONUNBUFFERED": "1"},
        )
        result.return_code = completed.returncode
        result.stdout_tail = tail_text(completed.stdout)
        result.stderr_tail = tail_text(completed.stderr)
        parsed = None
        parsed_source = None
        if spec.expected_json_path is not None:
            parsed = parse_json_file(spec.expected_json_path)
            if parsed is not None:
                parsed_source = str(spec.expected_json_path)
        if parsed is None:
            parsed = extract_first_json(completed.stdout)
            if parsed is not None:
                parsed_source = "stdout"
                if spec.expected_json_path is not None:
                    spec.expected_json_path.parent.mkdir(parents=True, exist_ok=True)
                    spec.expected_json_path.write_text(
                        json.dumps(parsed, indent=2, sort_keys=True) + "\n",
                        encoding="utf-8",
                    )
                    parsed_source = str(spec.expected_json_path)
        if parsed is None:
            kv_summary = parse_key_value_summary(completed.stdout)
            if kv_summary:
                parsed = {"text_key_value_summary": kv_summary}
                parsed_source = "stdout_key_value"
        result.parsed_json_summary = summarize_json(parsed) if parsed is not None else None
        result.parsed_json_source = parsed_source
    except subprocess.TimeoutExpired as exc:
        result.return_code = 124
        result.stdout_tail = tail_text(exc.stdout or "")
        result.stderr_tail = tail_text(exc.stderr or "")
        result.notes.append(f"timed out after {timeout_seconds}s")
    finally:
        result.duration_seconds = round(time.monotonic() - started, 6)

    return result


def build_manifest(results: list[HarnessResult], timeout_seconds: int) -> dict[str, Any]:
    failures = [
        result.name
        for result in results
        if not result.skipped and result.return_code not in (0, None)
    ]
    executed = [result for result in results if not result.skipped]
    skipped = [result for result in results if result.skipped]
    return {
        "control": {
            "O": "Local Clay diagnostic harness integration runner.",
            "R": "Discover and smoke-run local NS/YM/unification/Gray-Scott diagnostic harnesses.",
            "C": "scripts/local_clay_harness_manifest.py -> outputs/local_clay_harness_manifest.json",
            "S": "Diagnostics only; exact proof gates remain open.",
            "L": "discover -> smoke execute -> parse summaries -> fail-closed manifest",
            "P": "Use tiny local runs and preserve promotion=false globally and per harness.",
            "G": "No Clay, YM, NS, or unification promotion from numerical diagnostics.",
            "F": "Does not prove output width, compensated leakage, Hamiltonian domination, OS transfer, or parallelogram law.",
        },
        "promotion": False,
        "clay_promoted": False,
        "timeout_seconds_per_harness": timeout_seconds,
        "repo_root": str(REPO_ROOT),
        "output_path": str(DEFAULT_OUT),
        "summary": {
            "harnesses_total": len(results),
            "executed": len(executed),
            "skipped": len(skipped),
            "failures": failures,
            "all_executed_smokes_passed": not failures,
        },
        "results": [result.__dict__ for result in results],
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--timeout-seconds", type=int, default=DEFAULT_TIMEOUT_SECONDS)
    parser.add_argument("--json", action="store_true", help="print full manifest JSON")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.timeout_seconds <= 0:
        raise SystemExit("--timeout-seconds must be positive")

    specs = build_specs()
    results = [run_spec(spec, args.timeout_seconds) for spec in specs]
    manifest = build_manifest(results, args.timeout_seconds)
    manifest["output_path"] = str(args.out)

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if args.json:
        print(json.dumps(manifest, indent=2, sort_keys=True))
    else:
        summary = manifest["summary"]
        print("local Clay harness manifest")
        print(f"wrote: {args.out}")
        print(f"executed={summary['executed']} skipped={summary['skipped']} failures={summary['failures']}")
        print("promotion=false")

    return 0 if manifest["summary"]["all_executed_smokes_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
