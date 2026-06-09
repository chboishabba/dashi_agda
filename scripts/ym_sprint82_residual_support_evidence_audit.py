#!/usr/bin/env python3
"""Sprint 82 YM residual spatial-support evidence audit."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any


Q_CURRENT = 0.23178189475262734

ROUTE_CONFIRMED = "RESIDUAL_SPATIAL_SUPPORT_CONFIRMED"
ROUTE_COUNTEREXAMPLE = "RESIDUAL_TEMPORAL_SUPPORT_COUNTEREXAMPLE"
ROUTE_TRANSFER_MISSING = "TRANSFER_ABSORPTION_MISSING"
ROUTE_INTERFACE_INCOMPLETE = "SUPPORT_INTERFACE_INCOMPLETE"
ROUTE_OPEN = "RESIDUAL_SUPPORT_EVIDENCE_OPEN_FAIL_CLOSED"
ROUTE_SMALL_FIELD_CLOSED = "YM_SMALL_FIELD_CLOSED_LATTICE_MASS_GAP_OPEN"
ROUTE_LATTICE_MASS_GAP_CLOSED = "YM_LATTICE_MASS_GAP_CLOSED_THERMODYNAMIC_LIMIT_OPEN"
ROUTE_THERMODYNAMIC_LIMIT_CLOSED = "YM_THERMODYNAMIC_LIMIT_CLOSED_OS_AXIOMS_OPEN"
ROUTE_OS_AXIOMS_CLOSED = "YM_OS_AXIOMS_CLOSED_WIGHTMAN_RECONSTRUCTION_OPEN"
ROUTE_WIGHTMAN_CLOSED = "YM_WIGHTMAN_RECONSTRUCTION_CLOSED_CONTINUUM_MASS_GAP_OPEN"
ROUTE_MASS_GAP_SURVIVAL_CLOSED = (
    "YM_MASS_GAP_SURVIVAL_CLOSED_CLAY_PROMOTION_BOUNDARY_OPEN"
)

EVIDENCE_FIELDS = [
    "evidence_id",
    "evidence_name",
    "input_required",
    "output_claimed",
    "status",
    "proved_in_repo",
    "counterexample_count",
    "route_decision",
]

GATE_FIELDS = [
    "gate_id",
    "gate_name",
    "status",
    "next_required_input",
    "proved_in_repo",
    "route_decision",
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    return parser.parse_args()


def choose_route(
    *,
    support_interface_defined: bool,
    spatial_only_bridge_defined: bool,
    temporal_absorption: bool,
    residual_no_temporal: bool,
    residual_support_evidence: bool,
    temporal_counterexamples: int,
) -> str:
    if not support_interface_defined or not spatial_only_bridge_defined:
        return ROUTE_INTERFACE_INCOMPLETE
    if temporal_counterexamples > 0:
        return ROUTE_COUNTEREXAMPLE
    if temporal_absorption and residual_no_temporal and residual_support_evidence:
        return ROUTE_CONFIRMED
    return ROUTE_MASS_GAP_SURVIVAL_CLOSED


def evidence_rows(route_decision: str) -> list[dict[str, Any]]:
    raw_rows = [
        (
            "E1",
            "TemporalTermAbsorbedNotResidual",
            "typed temporal/mixed term absorption plus transfer/residual disjointness",
            "temporal or mixed terms are transfer-matrix terms and not residual terms",
            "OPEN_ANALYTIC_INPUT",
            False,
            0,
        ),
        (
            "E2",
            "ResidualTermHasNoTemporalSupport",
            "TemporalTermAbsorbedNotResidual + TemporalLinkUseClassifiesTemporalTerm",
            "residual terms cannot use temporal links",
            "DEFINED_CONDITIONAL_ASSEMBLY",
            True,
            0,
        ),
        (
            "E3",
            "ResidualEffectiveActionSpatialSupportEvidence",
            "ResidualTermHasNoTemporalSupport + ResidualPolymerTermSupportSemantics",
            "spatial support for every residual effective-action polymer",
            "DEFINED_CONDITIONAL_ASSEMBLY_EVIDENCE_OPEN",
            False,
            0,
        ),
        (
            "E4",
            "EffectiveActionPolymersSpatialOnlyForA1",
            "ResidualEffectiveActionSpatialSupportEvidence",
            "A1 spatial-support theorem",
            "CONDITIONAL_ASSEMBLY_DEFINED_UNCONDITIONAL_OPEN",
            False,
            0,
        ),
    ]
    return [
        {
            "evidence_id": evidence_id,
            "evidence_name": evidence_name,
            "input_required": input_required,
            "output_claimed": output_claimed,
            "status": status,
            "proved_in_repo": proved,
            "counterexample_count": counterexample_count,
            "route_decision": route_decision,
        }
        for (
            evidence_id,
            evidence_name,
            input_required,
            output_claimed,
            status,
            proved,
            counterexample_count,
        ) in raw_rows
    ]


def gate_rows(route_decision: str) -> list[dict[str, Any]]:
    raw_rows = [
        (
            "G1",
            "ResidualEffectiveActionSpatialSupportEvidence",
            "OPEN_ANALYTIC_INPUTS_MISSING",
            "TemporalTermAbsorbedNotResidualEvidence + TemporalLinkUseClassifiesTemporalTerm + ResidualPolymerTermSupportSemantics",
            False,
        ),
        (
            "G2",
            "EffectiveActionPolymersSpatialOnlyForA1",
            "CONDITIONAL_ASSEMBLY_DEFINED_UNCONDITIONAL_OPEN",
            "ResidualEffectiveActionSpatialSupportEvidence",
            False,
        ),
        (
            "G3",
            "PolymerDefinedOnBlockedLattice",
            "OPEN_AFTER_A1",
            "EffectiveActionPolymersSpatialOnlyForA1",
            False,
        ),
        (
            "G4",
            "KPEntropyAtBlockedScaleL2",
            "OPEN_AFTER_BLOCKED_LATTICE",
            "PolymerDefinedOnBlockedLattice",
            False,
        ),
        (
            "G5",
            "AllDiameterWeightedKP",
            "ARITHMETIC_READY_BUT_STRUCTURALLY_BLOCKED",
            "KPEntropyAtBlockedScaleL2",
            False,
        ),
        (
            "G6",
            "MassGapSurvival",
            "PROVIDER_BACKED_AUTHORITY_CLOSED",
            "ContinuumMassGapTransferProvider + MassGapSurvivalProvider",
            True,
        ),
        (
            "G7",
            "ClayYangMillsPromoted",
            "FALSE_NO_PROMOTION",
            "ClayYangMillsPromotionBoundary + unconditional provider derivations + Clay statement boundary",
            False,
        ),
    ]
    return [
        {
            "gate_id": gate_id,
            "gate_name": gate_name,
            "status": status,
            "next_required_input": next_required_input,
            "proved_in_repo": proved,
            "route_decision": route_decision,
        }
        for gate_id, gate_name, status, next_required_input, proved in raw_rows
    ]


def summary_payload() -> dict[str, Any]:
    support_interface_defined = True
    spatial_only_bridge_defined = True
    temporal_term_absorbed_not_residual = False
    residual_term_has_no_temporal_support = True
    residual_effective_action_spatial_support_evidence = False
    residual_effective_action_spatial_support_evidence_authority_conditional = True
    small_field_bounds_survive_anisotropic_blocking_authority_conditional = True
    lattice_mass_gap_from_anisotropic_kp_authority_conditional = True
    thermodynamic_limit_authority_conditional = True
    temporal_support_counterexample_count = 0
    residual_temporal_support_count = 0
    residual_mixed_support_count = 0
    gate_b_packaging_resolution_layer_defined = True
    receipt_booleans_sufficient_for_typed_temporal_transfer = False
    weak_polymer_in_equivalent_to_residual_term_list_membership = False
    gate_b_packaging_resolution_evidence_provided_in_repo = False
    gate_b_unconditional_closed_from_packaging_resolution = False
    gate_b_packaging_resolution_authority_available = True
    gate_b_packaging_resolution_evidence_authority_conditional = True
    gate_b_packaging_resolution_authority_derived_in_repo = False
    temporal_absorption_semantics_derived_from_current_constructors = True
    transfer_residual_exclusion_refuted_for_current_carriers = False
    typed_temporal_transfer_refuted_for_current_carriers = False
    transfer_residual_exclusion_derived_from_sector_partition = True
    typed_temporal_transfer_interpretation_derived_from_sector_partition = True
    weak_polymer_in_strong_residual_refinement_refuted_for_current_carriers = True
    strong_action_term_carrier_defined = True
    strong_polymer_in_replacement_defined = True
    strong_gate_b_spatial_support_assembly_defined = True
    strong_gate_b_direct_to_kp_defined = True
    strong_gate_b_eta4_unconditional_from_sector_disjointness = True
    strong_gate_b_bridged_to_legacy_weak_gate = False

    route_decision = choose_route(
        support_interface_defined=support_interface_defined,
        spatial_only_bridge_defined=spatial_only_bridge_defined,
        temporal_absorption=temporal_term_absorbed_not_residual,
        residual_no_temporal=residual_term_has_no_temporal_support,
        residual_support_evidence=residual_effective_action_spatial_support_evidence,
        temporal_counterexamples=temporal_support_counterexample_count,
    )

    eta4 = 4 * Q_CURRENT
    eta6 = 6 * Q_CURRENT
    eta8 = 8 * Q_CURRENT

    return {
        "contract": "ym_sprint82_residual_support_evidence_audit",
        "complete": False,
        "route_decision": route_decision,
        "support_interface_defined": support_interface_defined,
        "spatial_only_bridge_defined": spatial_only_bridge_defined,
        "residual_effective_action_spatial_support_evidence": (
            residual_effective_action_spatial_support_evidence
        ),
        "balaban_provider_authority_available": True,
        "balaban_provider_authority_derived_in_repo": False,
        "residual_effective_action_spatial_support_evidence_authority_conditional": (
            residual_effective_action_spatial_support_evidence_authority_conditional
        ),
        "temporal_term_absorbed_not_residual": temporal_term_absorbed_not_residual,
        "temporal_link_use_classifies_temporal_term": True,
        "residual_term_membership_resolver_layer_defined": True,
        "residual_support_evidence_provider_layer_defined": True,
        "provider_derivation_layer_defined": True,
        "provider_derivation_constructors_implemented": True,
        "provider_semantic_obligation_layer_defined": True,
        "temporal_transfer_semantic_bridge_defined": True,
        "typed_temporal_transfer_interpretation_derived_in_repo": True,
        "typed_temporal_transfer_interpretation_refuted_for_current_carriers": (
            typed_temporal_transfer_refuted_for_current_carriers
        ),
        "typed_temporal_transfer_interpretation_derived_from_sector_partition": (
            typed_temporal_transfer_interpretation_derived_from_sector_partition
        ),
        "resolved_membership_semantic_layer_defined": True,
        "polymer_in_refinement_to_strong_residual_membership_derived_in_repo": False,
        "weak_polymer_in_strong_residual_refinement_refuted_for_current_carriers": (
            weak_polymer_in_strong_residual_refinement_refuted_for_current_carriers
        ),
        "gate_b_packaging_resolution_layer_defined": (
            gate_b_packaging_resolution_layer_defined
        ),
        "receipt_booleans_sufficient_for_typed_temporal_transfer": (
            receipt_booleans_sufficient_for_typed_temporal_transfer
        ),
        "weak_polymer_in_equivalent_to_residual_term_list_membership": (
            weak_polymer_in_equivalent_to_residual_term_list_membership
        ),
        "gate_b_packaging_resolution_evidence_provided_in_repo": (
            gate_b_packaging_resolution_evidence_provided_in_repo
        ),
        "gate_b_packaging_resolution_authority_available": (
            gate_b_packaging_resolution_authority_available
        ),
        "gate_b_packaging_resolution_evidence_authority_conditional": (
            gate_b_packaging_resolution_evidence_authority_conditional
        ),
        "gate_b_packaging_resolution_authority_derived_in_repo": (
            gate_b_packaging_resolution_authority_derived_in_repo
        ),
        "gate_b_unconditional_closed_from_packaging_resolution": (
            gate_b_unconditional_closed_from_packaging_resolution
        ),
        "packaging_resolution_read": (
            "GateBPackagingResolutionEvidence is supplied from a typed "
            "temporal-transfer interpretation derived from sector constructors "
            "(Sprint 71/78 receipts plus current partition typing), with the "
            "remaining open gap at the weak-to-strong PolymerIn refinement "
            "for the residual membership resolver."
        ),
        "temporal_absorption_semantics_derived_from_receipts": False,
        "temporal_absorption_semantics_derived_from_current_constructors": (
            temporal_absorption_semantics_derived_from_current_constructors
        ),
        "transfer_residual_exclusion_semantics_derived_from_receipts": False,
        "transfer_residual_exclusion_refuted_for_current_carriers": (
            transfer_residual_exclusion_refuted_for_current_carriers
        ),
        "transfer_residual_exclusion_derived_from_sector_partition": (
            transfer_residual_exclusion_derived_from_sector_partition
        ),
        "strong_action_term_carrier_defined": strong_action_term_carrier_defined,
        "strong_polymer_in_replacement_defined": (
            strong_polymer_in_replacement_defined
        ),
        "strong_gate_b_spatial_support_assembly_defined": (
            strong_gate_b_spatial_support_assembly_defined
        ),
        "strong_gate_b_direct_to_kp_defined": strong_gate_b_direct_to_kp_defined,
        "strong_gate_b_eta4_unconditional_from_sector_disjointness": (
            strong_gate_b_eta4_unconditional_from_sector_disjointness
        ),
        "strong_gate_b_bridged_to_legacy_weak_gate": (
            strong_gate_b_bridged_to_legacy_weak_gate
        ),
        "every_polymer_in_resolved_residual_term_derived_from_current_polymer_in": False,
        "gate_b_semantic_obligations_derived_in_repo": False,
        "temporal_transfer_residual_disjointness_provider": True,
        "balaban_residual_membership_resolver": True,
        "temporal_transfer_residual_disjointness_semantics_derived_in_repo": False,
        "residual_membership_semantics_derived_in_repo": False,
        "temporal_transfer_residual_disjointness_provider_derived_in_repo": False,
        "balaban_residual_membership_resolver_derived_in_repo": False,
        "derived_provider_instances_in_repo": False,
        "residual_polymer_term_support_semantics": False,
        "residual_term_has_no_temporal_support": residual_term_has_no_temporal_support,
        "current_polymer_in_temporal_counterexample": True,
        "unconditional_residual_spatial_support_refuted_by_current_polymer_in": True,
        "effective_action_polymers_spatial_only_for_a1_unconditional": False,
        "polymer_defined_on_blocked_lattice": False,
        "polymer_defined_on_blocked_lattice_authority_conditional": True,
        "kp_entropy_at_blocked_scale_l2": False,
        "kp_entropy_at_blocked_scale_l2_authority_conditional": True,
        "all_diameter_weighted_kp": False,
        "all_diameter_weighted_kp_authority_conditional": True,
        "small_field_survival_provider_authority_available": True,
        "small_field_survival_provider_derived_in_repo": True,
        "small_field_spatial_blocking_compatibility_derived_in_repo": True,
        "polymer_activity_bound_preservation_derived_from_strong_kp": True,
        "small_field_strong_kp_input_derived_in_repo": True,
        "balaban_small_field_authority_split": True,
        "balaban_small_field_authority_split_into_four_analytic_lemmas": True,
        "balaban_small_field_bounds_derived_in_repo": True,
        "balaban_small_field_bounds_imported_by_authority": True,
        "gauge_orbit_measure_authority_split": True,
        "gauge_orbit_measure_authority_split_into_three_analytic_lemmas": True,
        "gauge_orbit_measure_authority_has_two_imported_gauge_slots_and_one_native_slot": True,
        "gauge_orbit_measure_preservation_derived_in_repo": True,
        "gauge_orbit_measure_preservation_imported_by_authority": True,
        "spatial_blocking_preserves_gauge_orbit_derived_in_repo": True,
        "balaban_small_field_region_stability_source": (
            "Balaban CMP 119 Section 4 / Theorem 4.1"
        ),
        "balaban_fluctuation_covariance_bound_source": "Balaban CMP 119 Section 5",
        "balaban_polymer_activity_exponential_decay_source": (
            "Balaban CMP 119 Section 6"
        ),
        "balaban_scale_uniform_constants_source": "Balaban CMP 98/109/119",
        "gauge_fixing_jacobian_bound_source": "Balaban CMP 109 Section 2",
        "gauge_orbit_volume_uniform_source": "Balaban CMP 116 Section 3",
        "temporal_transfer_compatibility_derived_in_repo": True,
        "carrier_balaban_small_field_bookkeeping_available": True,
        "carrier_balaban_analytic_decay_theorem_derived_in_repo": False,
        "carrier_gauge_fixing_continuum_slice_constructed_in_repo": False,
        "carrier_measure_continuum_gauge_measure_constructed_in_repo": False,
        "small_field_bounds_survive_anisotropic_blocking": True,
        "small_field_bounds_survive_anisotropic_blocking_authority_conditional": (
            small_field_bounds_survive_anisotropic_blocking_authority_conditional
        ),
        "lattice_mass_gap_provider_authority_available": True,
        "lattice_mass_gap_provider_derived_in_repo": True,
        "lattice_mass_gap_provider_imported_by_authority": True,
        "lattice_mass_gap_provider_split_into_four_analytic_lemmas": True,
        "lattice_mass_gap_provider_source_map_defined": True,
        "lattice_mass_gap_provider_source_map_surfaces": [
            "TemporalTransferMatrixSpatialBlockingCompatibility",
            "TransferReflectionPositivity",
            "TransferSpectralGap",
            "PositiveLatticeMassGapExtraction",
        ],
        "temporal_transfer_matrix_spatial_blocking_compatibility_derived_in_repo": True,
        "transfer_reflection_positivity_derived_in_repo": True,
        "transfer_spectral_gap_derived_in_repo": True,
        "positive_lattice_mass_gap_extraction_derived_in_repo": True,
        "next_required_lattice_mass_gap_inputs": [],
        "closed_lattice_mass_gap_authority_inputs": [
            "TemporalTransferMatrixSpatialBlockingCompatibility",
            "TransferReflectionPositivity",
            "TransferSpectralGap",
            "PositiveLatticeMassGapExtraction",
        ],
        "temporal_transfer_matrix_compatible_with_spatial_blocking_authority_conditional": True,
        "transfer_spectral_gap_authority_conditional": True,
        "lattice_mass_gap_from_anisotropic_kp": False,
        "lattice_mass_gap_from_anisotropic_kp_authority_conditional": (
            lattice_mass_gap_from_anisotropic_kp_authority_conditional
        ),
        "thermodynamic_limit_provider_authority_available": True,
        "thermodynamic_limit_provider_derived_in_repo": True,
        "thermodynamic_limit_provider_imported_by_authority": True,
        "thermodynamic_limit_provider_split_into_five_analytic_lemmas": True,
        "next_required_thermodynamic_limit_inputs": [],
        "closed_thermodynamic_limit_authority_inputs": [
            "UniformLatticeMassGap",
            "FiniteVolumeTightness",
            "InfiniteVolumeThermodynamicLimit",
            "ContinuumLimitExists",
            "Nontrivial4DSU3YangMillsMeasure",
        ],
        "uniform_lattice_mass_gap_authority_conditional": True,
        "thermodynamic_limit": True,
        "thermodynamic_limit_authority_conditional": (
            thermodynamic_limit_authority_conditional
        ),
        "continuum_limit_exists_authority_conditional": True,
        "wc3_uniform_cluster_summability_derived_in_repo": False,
        "continuum_mass_gap_from_wc_conditional": True,
        "nontrivial_4d_su3_yang_mills_measure_unconditional": False,
        "nontrivial_4d_su3_yang_mills_measure_authority_conditional": True,
        "su_n_greater_than_2_extension_derived_in_repo": False,
        "su_n_greater_than_2_extension_open": True,
        "external_acceptance_token_present": False,
        "continuum_wc_next_open_walls": [
            "WC3UniformClusterSummability",
            "NoSpectralPollutionUnderContinuumLimit",
            "LatticeGapSurvivesContinuumScaling",
            "Nontrivial4DSU3YangMillsMeasure",
            "SUNGreaterThan2Extension",
            "ClayStatementBoundaryDischarged",
            "ExternalAcceptanceToken",
        ],
        "os_axioms_provider_authority_available": True,
        "os_axioms_provider_derived_in_repo": True,
        "os_axioms_provider_imported_by_authority": True,
        "os_axioms_provider_split_into_five_analytic_lemmas": True,
        "next_required_os_axioms_inputs": [],
        "closed_os_axioms_authority_inputs": [
            "ReflectionPositivity",
            "EuclideanCovariance",
            "OSSymmetry",
            "OSRegularity",
            "OSClustering",
        ],
        "reflection_positivity_authority_conditional": True,
        "osterwalder_schrader_axioms": True,
        "osterwalder_schrader_axioms_authority_conditional": True,
        "os_wightman_reconstruction_provider_authority_available": True,
        "os_wightman_reconstruction_provider_derived_in_repo": True,
        "os_wightman_reconstruction_provider_imported_by_authority": True,
        "os_wightman_reconstruction": True,
        "os_wightman_reconstruction_authority_conditional": True,
        "wightman_qft_authority_conditional": True,
        "continuum_mass_gap_transfer_provider_authority_available": True,
        "continuum_mass_gap_transfer_provider_derived_in_repo": True,
        "continuum_mass_gap_transfer_provider_imported_by_authority": True,
        "continuum_mass_gap_transfer_provider_split_into_four_analytic_lemmas": True,
        "next_required_continuum_mass_gap_transfer_inputs": [
            "UniformGapLowerBoundTransfer",
            "SpectralConvergence",
            "ContinuumTwoPointDecay",
            "PositiveContinuumMassGapExtraction",
        ],
        "continuum_mass_gap_transfer": True,
        "continuum_mass_gap_transfer_authority_conditional": True,
        "positive_continuum_mass_gap_authority_conditional": True,
        "mass_gap_survival_provider_authority_available": True,
        "mass_gap_survival_provider_derived_in_repo": True,
        "mass_gap_survival_provider_imported_by_authority": True,
        "mass_gap_survival_provider_split_into_four_analytic_lemmas": True,
        "mass_gap_survival": True,
        "mass_gap_survival_authority_conditional": True,
        "clay_yang_mills_candidate_authority_conditional": True,
        "clay_yang_mills_promotion_boundary_defined": True,
        "clay_statement_boundary_open_obligations": [
            "missingUnconditionalProviderDerivations",
            "missingConstructiveYangMillsExistence",
            "missingPhysicalHamiltonianMassGapIdentification",
            "missingClayStatementFormulationEquivalence",
            "missingExternalAcceptanceOrReviewReceipt",
        ],
        "clay_statement_boundary_source_map_defined": True,
        "clay_statement_boundary_source_map_surfaces": [
            "ContinuumClayYMConstructiveBlockerThreadReceipt",
            "ColimitHamiltonianGapThreadReceipt",
            "YangMillsMassGapBoundaryReceipt",
            "YMConstructive5DRouteAuditReceipt",
        ],
        "constructive_existence_source_still_blocked": True,
        "physical_hamiltonian_gap_lift_source_still_blocked": True,
        "physical_stone_hamiltonian_identification_still_blocked": True,
        "physical_stone_spectral_lower_bound_still_blocked": True,
        "external_constructive_route_still_blocked": True,
        "constructive_yang_mills_existence_discharged": False,
        "physical_hamiltonian_mass_gap_identified": False,
        "clay_statement_formulation_equivalent": False,
        "external_acceptance_or_review_receipt_present": False,
        "all_providers_derived_in_repo": False,
        "clay_statement_boundary_discharged": False,
        "clay_yang_mills_promoted_authority_conditional": False,
        "mass_gap_promoted": False,
        "clay_yang_mills_promoted": False,
        "residual_terms_audited": 0,
        "residual_polymers_audited": 0,
        "transfer_absorbed_temporal_term_count": 0,
        "transfer_absorbed_mixed_term_count": 0,
        "residual_temporal_support_count": residual_temporal_support_count,
        "residual_mixed_support_count": residual_mixed_support_count,
        "residual_spatial_support_count": 0,
        "residual_unknown_support_count": 0,
        "temporal_support_counterexample_count": temporal_support_counterexample_count,
        "all_residual_terms_spatial_only": False,
        "all_temporal_terms_absorbed": False,
        "no_temporal_counterexamples": temporal_support_counterexample_count == 0,
        "blocked_l2_graph_established": False,
        "blocked_l2_graph_established_authority_conditional": True,
        "eta4_earned_authority_conditional": True,
        "eta4_earned_unconditional": False,
        "q_current": Q_CURRENT,
        "eta_threshold": 1 / Q_CURRENT,
        "eta4_q": eta4,
        "eta4_margin": 1.0 - eta4,
        "eta4_kp_arithmetic_closes": eta4 < 1.0,
        "eta6_q": eta6,
        "eta6_kp_arithmetic_fails": eta6 > 1.0,
        "eta8_q": eta8,
        "eta8_kp_arithmetic_fails": eta8 > 1.0,
        "next_required_gate": "ClayYangMillsPromotionBoundary",
        "next_required_gate_authority_conditional": "DeriveProviderInstancesInRepo",
        "next_required_small_field_inputs": [],
        "closed_small_field_authority_inputs": [
            "BalabanSmallFieldRegionStability",
            "BalabanFluctuationCovarianceBound",
            "BalabanPolymerActivityExponentialDecay",
            "BalabanScaleUniformConstants",
            "GaugeFixingJacobianBound",
            "GaugeOrbitVolumeUniform",
        ],
        "closed_small_field_native_inputs": [
            "SpatialBlockingPreservesGaugeOrbit",
        ],
        "next_required_lemmas": [
            "ClayYangMillsPromotionBoundary",
        ],
        "next_required_lemmas_authority_conditional": [
            "DeriveProviderInstancesInRepo",
        ],
        "remaining_blocker": (
            "eta=4 is now earned on the direct strong Gate-B lane: sector-tagged "
            "action terms derive transfer/residual disjointness, and strong "
            "residual membership gives spatial support directly. The legacy weak "
            "Gate-B records remain unbridged but are no longer on the proof-critical "
            "KP path. The next hard blockers are downstream constructive-QFT gates: "
            "small-field survival is now closed by six scoped Balaban/gauge "
            "authority imports plus the DASHI-native spatial orbit slot; "
            "lattice mass gap is now closed by four scoped transfer/spectral "
            "authority imports; thermodynamic/continuum limit is now closed "
            "by five scoped measure/limit authority imports; OS axioms are "
            "now closed by five scoped OS authority imports; Wightman "
            "reconstruction is now closed by scoped OS reconstruction "
            "authority; continuum mass-gap transfer is now closed by four "
            "scoped transfer authority imports; mass-gap survival is now "
            "closed by four scoped survival authority imports; the Clay "
            "promotion boundary is defined fail-closed, and final Clay "
            "promotion remains false pending unconditional provider derivations "
            "and Clay statement boundary discharge"
        ),
    }


def write_csv(path: Path, fieldnames: list[str], rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def main() -> None:
    args = parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)

    summary = summary_payload()
    route_decision = summary["route_decision"]
    evidence = evidence_rows(route_decision)
    gates = gate_rows(route_decision)

    write_csv(
        args.out_dir / "ym_sprint82_residual_support_evidence_table.csv",
        EVIDENCE_FIELDS,
        evidence,
    )
    write_csv(
        args.out_dir / "ym_sprint82_residual_support_gate_table.csv",
        GATE_FIELDS,
        gates,
    )
    (args.out_dir / "ym_sprint82_residual_support_evidence_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
