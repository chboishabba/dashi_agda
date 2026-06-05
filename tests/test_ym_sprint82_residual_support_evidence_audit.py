from __future__ import annotations

import csv
import json
import subprocess
import sys
from pathlib import Path


SCRIPT = Path("scripts/ym_sprint82_residual_support_evidence_audit.py")


def run_audit(tmp_path: Path) -> tuple[Path, dict]:
    out_dir = tmp_path / "sprint82"
    subprocess.run(
        [sys.executable, str(SCRIPT), "--out-dir", str(out_dir)],
        check=True,
        cwd=Path.cwd(),
    )
    summary = json.loads(
        (out_dir / "ym_sprint82_residual_support_evidence_summary.json").read_text()
    )
    return out_dir, summary


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        return list(csv.DictReader(handle))


def test_sprint82_outputs_and_schema(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)

    assert summary["contract"] == "ym_sprint82_residual_support_evidence_audit"
    assert (out_dir / "ym_sprint82_residual_support_evidence_table.csv").exists()
    assert (out_dir / "ym_sprint82_residual_support_gate_table.csv").exists()
    assert (out_dir / "ym_sprint82_residual_support_evidence_summary.json").exists()

    evidence_rows = read_csv(out_dir / "ym_sprint82_residual_support_evidence_table.csv")
    gate_rows = read_csv(out_dir / "ym_sprint82_residual_support_gate_table.csv")

    assert {row["evidence_name"] for row in evidence_rows} >= {
        "TemporalTermAbsorbedNotResidual",
        "ResidualTermHasNoTemporalSupport",
        "ResidualEffectiveActionSpatialSupportEvidence",
        "EffectiveActionPolymersSpatialOnlyForA1",
    }
    assert {row["gate_name"] for row in gate_rows} >= {
        "ResidualEffectiveActionSpatialSupportEvidence",
        "KPEntropyAtBlockedScaleL2",
        "MassGapSurvival",
        "ClayYangMillsPromoted",
    }


def test_sprint82_fail_closed_without_residual_support_evidence(
    tmp_path: Path,
) -> None:
    _out_dir, summary = run_audit(tmp_path)

    assert summary["complete"] is False
    assert (
        summary["route_decision"]
        == "YM_MASS_GAP_SURVIVAL_CLOSED_CLAY_PROMOTION_BOUNDARY_OPEN"
    )
    assert summary["support_interface_defined"] is True
    assert summary["spatial_only_bridge_defined"] is True
    assert summary["temporal_term_absorbed_not_residual"] is False
    assert summary["temporal_link_use_classifies_temporal_term"] is True
    assert summary["residual_term_membership_resolver_layer_defined"] is True
    assert summary["residual_support_evidence_provider_layer_defined"] is True
    assert summary["provider_derivation_layer_defined"] is True
    assert summary["provider_derivation_constructors_implemented"] is True
    assert summary["provider_semantic_obligation_layer_defined"] is True
    assert summary["temporal_transfer_semantic_bridge_defined"] is True
    assert summary["typed_temporal_transfer_interpretation_derived_in_repo"] is True
    assert (
        summary["typed_temporal_transfer_interpretation_refuted_for_current_carriers"]
        is False
    )
    assert (
        summary["typed_temporal_transfer_interpretation_derived_from_sector_partition"]
        is True
    )
    assert summary["resolved_membership_semantic_layer_defined"] is True
    assert (
        summary["polymer_in_refinement_to_strong_residual_membership_derived_in_repo"]
        is False
    )
    assert (
        summary[
            "weak_polymer_in_strong_residual_refinement_refuted_for_current_carriers"
        ]
        is True
    )
    assert summary["gate_b_packaging_resolution_layer_defined"] is True
    assert (
        summary["receipt_booleans_sufficient_for_typed_temporal_transfer"]
        is False
    )
    assert (
        summary["weak_polymer_in_equivalent_to_residual_term_list_membership"]
        is False
    )
    assert (
        summary["gate_b_packaging_resolution_evidence_provided_in_repo"]
        is False
    )
    assert summary["gate_b_packaging_resolution_authority_available"] is True
    assert (
        summary["gate_b_packaging_resolution_evidence_authority_conditional"]
        is True
    )
    assert (
        summary["gate_b_packaging_resolution_authority_derived_in_repo"]
        is False
    )
    assert (
        summary["gate_b_unconditional_closed_from_packaging_resolution"]
        is False
    )
    assert (
        "weak-to-strong PolymerIn refinement"
        in summary["packaging_resolution_read"]
    )
    assert summary["temporal_absorption_semantics_derived_from_receipts"] is False
    assert (
        summary["temporal_absorption_semantics_derived_from_current_constructors"]
        is True
    )
    assert summary["transfer_residual_exclusion_semantics_derived_from_receipts"] is False
    assert (
        summary["transfer_residual_exclusion_refuted_for_current_carriers"]
        is False
    )
    assert (
        summary["transfer_residual_exclusion_derived_from_sector_partition"]
        is True
    )
    assert summary["strong_action_term_carrier_defined"] is True
    assert summary["strong_polymer_in_replacement_defined"] is True
    assert summary["strong_gate_b_spatial_support_assembly_defined"] is True
    assert summary["strong_gate_b_direct_to_kp_defined"] is True
    assert (
        summary["strong_gate_b_eta4_unconditional_from_sector_disjointness"]
        is True
    )
    assert summary["strong_gate_b_bridged_to_legacy_weak_gate"] is False
    assert (
        summary["every_polymer_in_resolved_residual_term_derived_from_current_polymer_in"]
        is False
    )
    assert summary["gate_b_semantic_obligations_derived_in_repo"] is False
    assert summary["balaban_provider_authority_available"] is True
    assert summary["balaban_provider_authority_derived_in_repo"] is False
    assert summary["temporal_transfer_residual_disjointness_provider"] is True
    assert summary["balaban_residual_membership_resolver"] is True
    assert (
        summary["temporal_transfer_residual_disjointness_semantics_derived_in_repo"]
        is False
    )
    assert summary["residual_membership_semantics_derived_in_repo"] is False
    assert summary["temporal_transfer_residual_disjointness_provider_derived_in_repo"] is False
    assert summary["balaban_residual_membership_resolver_derived_in_repo"] is False
    assert summary["derived_provider_instances_in_repo"] is False
    assert (
        summary["residual_effective_action_spatial_support_evidence_authority_conditional"]
        is True
    )
    assert summary["current_polymer_in_temporal_counterexample"] is True
    assert (
        summary["unconditional_residual_spatial_support_refuted_by_current_polymer_in"]
        is True
    )
    assert summary["residual_effective_action_spatial_support_evidence"] is False
    assert summary["effective_action_polymers_spatial_only_for_a1_unconditional"] is False
    assert summary["polymer_defined_on_blocked_lattice"] is False
    assert summary["polymer_defined_on_blocked_lattice_authority_conditional"] is True
    assert summary["kp_entropy_at_blocked_scale_l2"] is False
    assert summary["kp_entropy_at_blocked_scale_l2_authority_conditional"] is True
    assert summary["all_diameter_weighted_kp"] is False
    assert summary["all_diameter_weighted_kp_authority_conditional"] is True
    assert summary["small_field_survival_provider_authority_available"] is True
    assert summary["small_field_survival_provider_derived_in_repo"] is True
    assert summary["small_field_spatial_blocking_compatibility_derived_in_repo"] is True
    assert summary["polymer_activity_bound_preservation_derived_from_strong_kp"] is True
    assert summary["small_field_strong_kp_input_derived_in_repo"] is True
    assert summary["balaban_small_field_authority_split"] is True
    assert summary["balaban_small_field_bounds_derived_in_repo"] is True
    assert summary["balaban_small_field_bounds_imported_by_authority"] is True
    assert summary["gauge_orbit_measure_authority_split"] is True
    assert summary["gauge_orbit_measure_preservation_derived_in_repo"] is True
    assert summary["gauge_orbit_measure_preservation_imported_by_authority"] is True
    assert (
        summary["spatial_blocking_preserves_gauge_orbit_derived_in_repo"]
        is True
    )
    assert summary["temporal_transfer_compatibility_derived_in_repo"] is True
    assert summary["small_field_bounds_survive_anisotropic_blocking"] is True
    assert (
        summary["small_field_bounds_survive_anisotropic_blocking_authority_conditional"]
        is True
    )
    assert summary["lattice_mass_gap_provider_authority_available"] is True
    assert summary["lattice_mass_gap_provider_derived_in_repo"] is False
    assert summary["lattice_mass_gap_provider_imported_by_authority"] is True
    assert summary["lattice_mass_gap_provider_split_into_four_analytic_lemmas"] is True
    assert summary["lattice_mass_gap_provider_source_map_defined"] is True
    assert summary["lattice_mass_gap_provider_source_map_surfaces"] == [
        "TemporalTransferMatrixSpatialBlockingCompatibility",
        "TransferReflectionPositivity",
        "TransferSpectralGap",
        "PositiveLatticeMassGapExtraction",
    ]
    assert (
        summary[
            "temporal_transfer_matrix_spatial_blocking_compatibility_derived_in_repo"
        ]
        is False
    )
    assert summary["transfer_reflection_positivity_derived_in_repo"] is False
    assert summary["transfer_spectral_gap_derived_in_repo"] is False
    assert (
        summary["positive_lattice_mass_gap_extraction_derived_in_repo"]
        is False
    )
    assert summary["next_required_lattice_mass_gap_inputs"] == [
        "TemporalTransferMatrixSpatialBlockingCompatibility",
        "TransferReflectionPositivity",
        "TransferSpectralGap",
        "PositiveLatticeMassGapExtraction",
    ]
    assert summary["closed_lattice_mass_gap_authority_inputs"] == [
        "TemporalTransferMatrixSpatialBlockingCompatibility",
        "TransferReflectionPositivity",
        "TransferSpectralGap",
        "PositiveLatticeMassGapExtraction",
    ]
    assert (
        summary[
            "temporal_transfer_matrix_compatible_with_spatial_blocking_authority_conditional"
        ]
        is True
    )
    assert summary["transfer_spectral_gap_authority_conditional"] is True
    assert summary["lattice_mass_gap_from_anisotropic_kp"] is False
    assert summary["lattice_mass_gap_from_anisotropic_kp_authority_conditional"] is True
    assert summary["thermodynamic_limit_provider_authority_available"] is True
    assert summary["thermodynamic_limit_provider_derived_in_repo"] is True
    assert summary["thermodynamic_limit_provider_imported_by_authority"] is True
    assert summary["thermodynamic_limit_provider_split_into_five_analytic_lemmas"] is True
    assert summary["next_required_thermodynamic_limit_inputs"] == []
    assert summary["closed_thermodynamic_limit_authority_inputs"] == [
        "UniformLatticeMassGap",
        "FiniteVolumeTightness",
        "InfiniteVolumeThermodynamicLimit",
        "ContinuumLimitExists",
        "Nontrivial4DSU3YangMillsMeasure",
    ]
    assert summary["uniform_lattice_mass_gap_authority_conditional"] is True
    assert summary["thermodynamic_limit"] is True
    assert summary["thermodynamic_limit_authority_conditional"] is True
    assert summary["continuum_limit_exists_authority_conditional"] is True
    assert (
        summary["nontrivial_4d_su3_yang_mills_measure_authority_conditional"]
        is True
    )
    assert summary["os_axioms_provider_authority_available"] is True
    assert summary["os_axioms_provider_derived_in_repo"] is True
    assert summary["os_axioms_provider_imported_by_authority"] is True
    assert summary["os_axioms_provider_split_into_five_analytic_lemmas"] is True
    assert summary["next_required_os_axioms_inputs"] == []
    assert summary["closed_os_axioms_authority_inputs"] == [
        "ReflectionPositivity",
        "EuclideanCovariance",
        "OSSymmetry",
        "OSRegularity",
        "OSClustering",
    ]
    assert summary["reflection_positivity_authority_conditional"] is True
    assert summary["osterwalder_schrader_axioms"] is True
    assert summary["osterwalder_schrader_axioms_authority_conditional"] is True
    assert summary["os_wightman_reconstruction_provider_authority_available"] is True
    assert summary["os_wightman_reconstruction_provider_derived_in_repo"] is True
    assert (
        summary["os_wightman_reconstruction_provider_imported_by_authority"]
        is True
    )
    assert summary["os_wightman_reconstruction"] is True
    assert summary["os_wightman_reconstruction_authority_conditional"] is True
    assert summary["wightman_qft_authority_conditional"] is True
    assert summary["continuum_mass_gap_transfer_provider_authority_available"] is True
    assert summary["continuum_mass_gap_transfer_provider_derived_in_repo"] is True
    assert (
        summary["continuum_mass_gap_transfer_provider_imported_by_authority"]
        is True
    )
    assert (
        summary[
            "continuum_mass_gap_transfer_provider_split_into_four_analytic_lemmas"
        ]
        is True
    )
    assert summary["next_required_continuum_mass_gap_transfer_inputs"] == [
        "UniformGapLowerBoundTransfer",
        "SpectralConvergence",
        "ContinuumTwoPointDecay",
        "PositiveContinuumMassGapExtraction",
    ]
    assert summary["continuum_mass_gap_transfer"] is True
    assert summary["continuum_mass_gap_transfer_authority_conditional"] is True
    assert summary["positive_continuum_mass_gap_authority_conditional"] is True
    assert summary["mass_gap_survival_provider_authority_available"] is True
    assert summary["mass_gap_survival_provider_derived_in_repo"] is True
    assert summary["mass_gap_survival_provider_imported_by_authority"] is True
    assert summary["mass_gap_survival_provider_split_into_four_analytic_lemmas"] is True
    assert summary["mass_gap_survival"] is True
    assert summary["mass_gap_survival_authority_conditional"] is True
    assert summary["clay_yang_mills_candidate_authority_conditional"] is True
    assert summary["clay_yang_mills_promotion_boundary_defined"] is True
    assert summary["clay_statement_boundary_open_obligations"] == [
        "missingUnconditionalProviderDerivations",
        "missingConstructiveYangMillsExistence",
        "missingPhysicalHamiltonianMassGapIdentification",
        "missingClayStatementFormulationEquivalence",
        "missingExternalAcceptanceOrReviewReceipt",
    ]
    assert summary["clay_statement_boundary_source_map_defined"] is True
    assert summary["clay_statement_boundary_source_map_surfaces"] == [
        "ContinuumClayYMConstructiveBlockerThreadReceipt",
        "ColimitHamiltonianGapThreadReceipt",
        "YangMillsMassGapBoundaryReceipt",
        "YMConstructive5DRouteAuditReceipt",
    ]
    assert summary["constructive_existence_source_still_blocked"] is True
    assert summary["physical_hamiltonian_gap_lift_source_still_blocked"] is True
    assert (
        summary["physical_stone_hamiltonian_identification_still_blocked"]
        is True
    )
    assert summary["physical_stone_spectral_lower_bound_still_blocked"] is True
    assert summary["external_constructive_route_still_blocked"] is True
    assert summary["constructive_yang_mills_existence_discharged"] is False
    assert summary["physical_hamiltonian_mass_gap_identified"] is False
    assert summary["clay_statement_formulation_equivalent"] is False
    assert summary["external_acceptance_or_review_receipt_present"] is False
    assert summary["all_providers_derived_in_repo"] is False
    assert summary["clay_statement_boundary_discharged"] is False
    assert summary["clay_yang_mills_promoted_authority_conditional"] is False
    assert summary["clay_yang_mills_promoted"] is False


def test_sprint82_support_counterexample_guardrails(tmp_path: Path) -> None:
    _out_dir, summary = run_audit(tmp_path)

    assert summary["residual_temporal_support_count"] == 0
    assert summary["residual_mixed_support_count"] == 0
    assert summary["temporal_support_counterexample_count"] == 0
    assert summary["no_temporal_counterexamples"] is True
    assert summary["all_residual_terms_spatial_only"] is False
    assert summary["all_temporal_terms_absorbed"] is False
    assert summary["blocked_l2_graph_established"] is False
    assert summary["blocked_l2_graph_established_authority_conditional"] is True
    assert summary["eta4_earned_authority_conditional"] is True
    assert summary["eta4_earned_unconditional"] is True


def test_sprint82_kp_arithmetic_guardrails_preserved(tmp_path: Path) -> None:
    _out_dir, summary = run_audit(tmp_path)

    assert summary["q_current"] == 0.23178189475262734
    assert summary["eta4_q"] == 0.9271275790105094
    assert summary["eta4_margin"] == 0.07287242098949065
    assert summary["eta4_kp_arithmetic_closes"] is True
    assert summary["eta6_q"] == 1.390691368515764
    assert summary["eta6_kp_arithmetic_fails"] is True
    assert summary["eta8_q"] == 1.8542551580210187
    assert summary["eta8_kp_arithmetic_fails"] is True


def test_sprint82_next_required_gate_progression(tmp_path: Path) -> None:
    _out_dir, summary = run_audit(tmp_path)

    assert summary["next_required_gate"] == "ClayYangMillsPromotionBoundary"
    assert summary["next_required_lemmas"] == [
        "ClayYangMillsPromotionBoundary",
    ]
    assert summary["next_required_gate_authority_conditional"] == (
        "DeriveProviderInstancesInRepo"
    )
    assert summary["next_required_small_field_inputs"] == []
    assert summary["closed_small_field_authority_inputs"] == [
        "BalabanSmallFieldRegionStability",
        "BalabanFluctuationCovarianceBound",
        "BalabanPolymerActivityExponentialDecay",
        "BalabanScaleUniformConstants",
        "GaugeFixingJacobianBound",
        "GaugeOrbitVolumeUniform",
    ]
    assert summary["closed_small_field_native_inputs"] == [
        "SpatialBlockingPreservesGaugeOrbit",
    ]
    assert summary["balaban_small_field_authority_split_into_four_analytic_lemmas"] is True
    assert summary["gauge_orbit_measure_authority_split_into_three_analytic_lemmas"] is True
    assert (
        summary[
            "gauge_orbit_measure_authority_has_two_imported_gauge_slots_and_one_native_slot"
        ]
        is True
    )
    assert (
        summary["balaban_small_field_region_stability_source"]
        == "Balaban CMP 119 Section 4 / Theorem 4.1"
    )
    assert summary["gauge_fixing_jacobian_bound_source"] == (
        "Balaban CMP 109 Section 2"
    )
    assert summary["carrier_balaban_small_field_bookkeeping_available"] is True
    assert summary["carrier_balaban_analytic_decay_theorem_derived_in_repo"] is False
    assert summary["carrier_gauge_fixing_continuum_slice_constructed_in_repo"] is False
    assert summary["carrier_measure_continuum_gauge_measure_constructed_in_repo"] is False
    assert summary["next_required_lemmas_authority_conditional"][:1] == [
        "DeriveProviderInstancesInRepo",
    ]
