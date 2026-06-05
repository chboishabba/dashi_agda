#!/usr/bin/env python3
"""Sprint 79 YM current-state to complete-roadmap audit."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any


Q_CURRENT = 0.23178189475262734
ETA_BLOCKED_L2 = 4
ETA_FINE_LATTICE_SPATIAL = 6
ETA_GENERIC_4D = 8

ETA4_Q = ETA_BLOCKED_L2 * Q_CURRENT
ETA6_Q = ETA_FINE_LATTICE_SPATIAL * Q_CURRENT
ETA8_Q = ETA_GENERIC_4D * Q_CURRENT

ETA4_MARGIN = 1.0 - ETA4_Q
ETA6_OVERSHOOT = ETA6_Q - 1.0
ETA8_OVERSHOOT = ETA8_Q - 1.0
ETA6_Q_THRESHOLD = 1.0 / ETA_FINE_LATTICE_SPATIAL
ETA6_Q_REDUCTION_NEEDED_PERCENT = (
    (Q_CURRENT - ETA6_Q_THRESHOLD) / Q_CURRENT * 100.0
)

ISOTROPIC_SPACETIME_LINK_DIMENSION = 4
ANISOTROPIC_SPATIAL_LINK_MULTIPLICITY = 3
ISOTROPIC_LINK_COUNT_FORM = "4*L^(4k)"
ANISOTROPIC_LINK_COUNT_FORM = "3*L^(3k)"
OSCILLATION_DECAY_FORM = "L^(-4k)"
ANISOTROPIC_UV_VOLUME_BALANCE = "L^(-4k)*3*L^(3k)=3*L^(-k)"
ERIKSSON_2602_0077_ASSUMPTION_A_STATUS = "OPEN_FOR_HALF_PLANE_BLOCKING"

GATE_FIELDS = [
    "gate_id",
    "gate_name",
    "depends_on",
    "current_status",
    "completion_condition",
    "proved_in_repo",
    "blocks_clay_promotion",
    "route_decision",
]

ROUTE_BLOCKED = "ANISOTROPIC_KP_ROUTE_BLOCKED"
ROUTE_STRONG_KP_CLOSED = "STRONG_GATE_B_TO_KP_CLOSED_NEXT_BLOCKER_SMALL_FIELD_SURVIVAL"
ROUTE_CONDITIONAL = "KP_GRAPH_IS_BLOCKED_L2_ETA4_CONFIRMED_CONDITIONAL"
ROUTE_UV_BLOCKED = "ANISOTROPIC_ASSUMPTION_A_OPEN_FAIL_CLOSED"
ROUTE_UV_CONDITIONAL = "UV_CLOSURE_AVAILABLE_IF_ANISOTROPIC_ASSUMPTION_A"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    return parser.parse_args()


def gate_rows() -> list[dict[str, Any]]:
    raw_rows = [
        (
            "G0",
            "NcAbsorptionFloorAuthority",
            "",
            "CITED_ASSUMED_NOT_FORMALLY_DERIVED",
            "primary-source authority formalized or accepted as explicit axiom",
            False,
            True,
            ROUTE_BLOCKED,
        ),
        (
            "G1",
            "EffectiveActionPolymersSpatialOnlyForA1",
            "G0",
            "OPEN",
            "all residual effective-action polymers have spatial support only",
            False,
            True,
            ROUTE_BLOCKED,
        ),
        (
            "G2",
            "PolymerDefinedOnBlockedLattice",
            "G1",
            "OPEN",
            "residual KP polymers are defined on the blocked L=2 graph",
            False,
            True,
            ROUTE_BLOCKED,
        ),
        (
            "G3",
            "KPEntropyAtBlockedScaleL2",
            "G1,G2",
            "OPEN",
            "blocked L=2 orientation count proves eta=4",
            False,
            True,
            ROUTE_BLOCKED,
        ),
        (
            "G4",
            "TemporalEntropyQuotientHalvesGeneric4DCount",
            "G1,G2,G3",
            "OPEN",
            "etaGeneric4D=8 is replaced by etaSpatialTransfer=4",
            False,
            True,
            ROUTE_BLOCKED,
        ),
        (
            "G5",
            "AnisotropicL2WeightedKPCloses",
            "G4",
            "ARITHMETIC_ONLY_CONDITIONAL",
            "eta=4 made proof-bearing and 4q<1 consumed by KP theorem",
            False,
            True,
            ROUTE_CONDITIONAL,
        ),
        (
            "G6",
            "AllDiameterWeightedKP",
            "G5",
            "AUTHORITY_CONDITIONAL",
            "summable all-diameter weighted polymer expansion available on the eta=4 authority lane",
            False,
            True,
            ROUTE_CONDITIONAL,
        ),
        (
            "G7",
            "BalabanPackageA1A2A3",
            "G1,G6",
            "OPEN",
            "Balaban/Eriksson A1-A3 package discharged",
            False,
            True,
            ROUTE_BLOCKED,
        ),
        (
            "G8",
            "SmallFieldBoundsSurviveAnisotropicBlocking",
            "G7",
            "AUTHORITY_CONDITIONAL",
            "uniform small-field bounds survive spatial-only blocking on explicit provider authority",
            False,
            True,
            ROUTE_CONDITIONAL,
        ),
        (
            "G9",
            "BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix",
            "G7",
            "OPEN",
            "Balaban partition identity commutes with temporal trace",
            False,
            True,
            ROUTE_BLOCKED,
        ),
        (
            "G10",
            "TemporalTransferMatrixCompatibleWithSpatialBlocking",
            "G8,G9",
            "OPEN",
            "spatial blocking preserves transfer-matrix spectral setup",
            False,
            True,
            ROUTE_BLOCKED,
        ),
        (
            "G11",
            "TransferSpectralGap",
            "G6,G8,G10",
            "OPEN",
            "positive transfer spectral gap proved on the lattice",
            False,
            True,
            ROUTE_BLOCKED,
        ),
        (
            "G12",
            "LatticeMassGapFromAnisotropicKP",
            "G11",
            "AUTHORITY_CONDITIONAL",
            "positive lattice mass gap extracted from anisotropic KP package on explicit transfer spectral-gap provider authority",
            False,
            True,
            ROUTE_CONDITIONAL,
        ),
        (
            "G13",
            "UniformLatticeMassGap",
            "G12",
            "OPEN",
            "uniform positive lattice mass gap established",
            False,
            True,
            ROUTE_BLOCKED,
        ),
        (
            "G14a",
            "PublishedArchitecture26020077",
            "",
            "CITED_ARCHITECTURE",
            (
                "Eriksson 2602.0077 Theorem 1.6 recorded as fixed-volume "
                "blocked-observable UV closure conditional on Assumption A"
            ),
            False,
            True,
            ROUTE_UV_BLOCKED,
        ),
        (
            "G14b",
            "IsotropicRGCauchyHypothesesDischarged",
            "G14a",
            "PUBLISHED_DISCHARGED_NOT_REPROVED_IN_REPO",
            (
                "polymer representation, oscillation decay, lattice animal "
                "count, large-field suppression, and Doob influence bound "
                "recorded from Balaban/Eriksson"
            ),
            False,
            True,
            ROUTE_UV_BLOCKED,
        ),
        (
            "G14c",
            "SharedAnisotropicInputLayer",
            "G1,G8,G10,G14a",
            "OPEN",
            (
                "spatial-only blocking, transfer-face absorption, temporal "
                "support non-creation, and Balaban averaging locality assembled"
            ),
            False,
            True,
            ROUTE_UV_BLOCKED,
        ),
        (
            "G14d0",
            "FormalOscillationSeminormForGaugeLinks",
            "G14c",
            "OPEN",
            "gauge-link oscillation seminorm osc_e defined for blocking-map observables",
            False,
            True,
            ROUTE_UV_BLOCKED,
        ),
        (
            "G14d1",
            "FormalQhpBlockingMapDefinition",
            "G14c",
            "OPEN",
            "formal half-plane/spatial Balaban averaging map Q_hp_{ell,k}",
            False,
            True,
            ROUTE_UV_BLOCKED,
        ),
        (
            "G14d2",
            "BalabanCMP98AveragingLocalityImported",
            "G14d0,G14d1",
            "OPEN",
            "primary CMP 98 averaging locality imported as a typed repo lemma",
            False,
            True,
            ROUTE_UV_BLOCKED,
        ),
        (
            "G14d3",
            "QhpPerLinkInfluenceConeLMinus2k",
            "G14d0,G14d1,G14d2",
            "OPEN",
            "Q_hp per-link influence cone gives L^(-2k) oscillation decay",
            False,
            True,
            ROUTE_UV_BLOCKED,
        ),
        (
            "G14d",
            "BalabanCMP98LocalOscillationBoundForQhp",
            "G14d0,G14d1,G14d2,G14d3",
            "OPEN",
            "CMP 98 averaging locality specialized to osc_e(Q_hp)<=C_local*L^(-2k)",
            False,
            True,
            ROUTE_UV_BLOCKED,
        ),
        (
            "G14e",
            "LipschitzToSquaredOscillationForQhp",
            "G14d",
            "OPEN",
            "per-link Q_hp locality converted into squared oscillation for F o Q_hp",
            False,
            True,
            ROUTE_UV_BLOCKED,
        ),
        (
            "G14f",
            "AnisotropicAssumptionA",
            "G14c,G14d,G14e",
            "OPEN",
            (
                "half-plane/spatial-only blocking map satisfies squared "
                "oscillation summability"
            ),
            False,
            True,
            ROUTE_UV_BLOCKED,
        ),
        (
            "G14g",
            "SquaredOscillationSummabilityForHalfPlaneBlocking",
            "G14f",
            "OPEN",
            "sum_e osc_e(F o Q_hp)^2 <= C_Q * Lip(F)^2 over spatial links",
            False,
            True,
            ROUTE_UV_BLOCKED,
        ),
        (
            "G14h",
            "AnisotropicSpatialLinkCountImprovesUVBalance",
            "G14g",
            "ARITHMETIC_ONLY_CONDITIONAL",
            "spatial link count 3*L^(3k) with L^(-4k) decay yields 3*L^(-k)",
            False,
            True,
            ROUTE_UV_CONDITIONAL,
        ),
        (
            "G14",
            "ContinuumLimitExists",
            "G14a,G14b,G14f,G14g",
            "AUTHORITY_CONDITIONAL",
            "fixed/infinite-volume blocked-observable continuum limit exists on explicit thermodynamic-limit provider authority",
            False,
            True,
            ROUTE_UV_CONDITIONAL,
        ),
        (
            "G15",
            "OSAxioms",
            "G14",
            "AUTHORITY_CONDITIONAL",
            "continuum limit satisfies Osterwalder-Schrader axioms on explicit OS provider authority",
            False,
            True,
            ROUTE_CONDITIONAL,
        ),
        (
            "G16",
            "Nontrivial4DSU3YangMillsMeasure",
            "G14",
            "OPEN",
            "nontrivial four-dimensional SU(3) Yang-Mills measure constructed",
            False,
            True,
            ROUTE_BLOCKED,
        ),
        (
            "G17",
            "ContinuumMassGapTransfer",
            "G13,G14,G15",
            "AUTHORITY_CONDITIONAL",
            "continuum limit transfers positive lattice mass gap on explicit transfer provider authority",
            False,
            True,
            ROUTE_CONDITIONAL,
        ),
        (
            "G18",
            "OSWightmanReconstruction",
            "G15,G17",
            "AUTHORITY_CONDITIONAL",
            "OS axioms reconstruct Wightman QFT on explicit reconstruction provider authority",
            False,
            True,
            ROUTE_CONDITIONAL,
        ),
        (
            "G19",
            "WightmanQFT",
            "G18",
            "AUTHORITY_CONDITIONAL",
            "Wightman QFT reconstructed on the OS/Wightman authority lane",
            False,
            True,
            ROUTE_CONDITIONAL,
        ),
        (
            "G20",
            "PositiveContinuumMassGap",
            "G17",
            "AUTHORITY_CONDITIONAL",
            "positive continuum mass gap available on continuum transfer authority lane",
            False,
            True,
            ROUTE_CONDITIONAL,
        ),
        (
            "G21",
            "MassGapSurvival",
            "G19,G20",
            "AUTHORITY_CONDITIONAL",
            "mass-gap survival theorem available on explicit survival provider authority",
            False,
            True,
            ROUTE_CONDITIONAL,
        ),
        (
            "G22",
            "ClayYangMills",
            "G19,G20,G21",
            "BLOCKED_FAIL_CLOSED_BOUNDARY_DEFINED",
            "authority-conditional candidate recorded, but promotion requires provider derivations in repo",
            False,
            True,
            ROUTE_BLOCKED,
        ),
    ]
    return [
        {
            "gate_id": gate_id,
            "gate_name": gate_name,
            "depends_on": depends_on,
            "current_status": current_status,
            "completion_condition": completion_condition,
            "proved_in_repo": proved,
            "blocks_clay_promotion": blocks,
            "route_decision": route,
        }
        for (
            gate_id,
            gate_name,
            depends_on,
            current_status,
            completion_condition,
            proved,
            blocks,
            route,
        ) in raw_rows
    ]


def summary_payload() -> dict[str, Any]:
    next_required_lemmas = [
        "SmallFieldBoundsSurviveAnisotropicBlocking",
        "LatticeMassGapFromAnisotropicKP",
        "ThermodynamicLimit",
        "OsterwalderSchraderAxioms",
        "OSWightmanReconstruction",
        "ContinuumMassGapTransfer",
        "MassGapSurvival",
    ]
    return {
        "contract": "ym_sprint79_current_to_complete_roadmap",
        "gate_table": "ym_sprint79_current_to_complete_gate_table.csv",
        "roadmap_status": "ym_sprint79_roadmap_status.json",
        "q_current": Q_CURRENT,
        "eta_blocked_l2": ETA_BLOCKED_L2,
        "eta_blocked_l2_q": ETA4_Q,
        "eta_blocked_l2_margin": ETA4_MARGIN,
        "eta_fine_lattice_spatial": ETA_FINE_LATTICE_SPATIAL,
        "eta_fine_lattice_spatial_q": ETA6_Q,
        "eta_fine_lattice_spatial_overshoot": ETA6_OVERSHOOT,
        "eta_generic_4d": ETA_GENERIC_4D,
        "eta_generic_4d_q": ETA8_Q,
        "eta_generic_4d_overshoot": ETA8_OVERSHOOT,
        "eta6_q_threshold": ETA6_Q_THRESHOLD,
        "eta6_q_reduction_needed_percent": ETA6_Q_REDUCTION_NEEDED_PERCENT,
        "published_uv_closure_architecture_2602_0077_recorded": True,
        "eriksson_2602_0077_theorem_1_6_status": "CONDITIONAL_ON_ASSUMPTION_A",
        "eriksson_2602_0077_theorem_1_6_conditional": True,
        "eriksson_2602_0077_open_assumption": "AssumptionA",
        "eriksson_2602_0077_assumption_a_status": ERIKSSON_2602_0077_ASSUMPTION_A_STATUS,
        "eriksson_2602_0077_polymer_representation_hypothesis_a_discharged": True,
        "polymer_representation_a1_discharged_by_balaban_eriksson": True,
        "polymer_representation_a1_is_not_open_assumption_a": True,
        "anisotropic_assumption_a": False,
        "anisotropic_assumption_a_fail_closed": True,
        "anisotropic_assumption_a_source": "Eriksson 2602.0077 Theorem 1.6 and Section 8.2",
        "anisotropic_assumption_a_blocking_map": "Q_hp_half_plane_spatial_only",
        "anisotropic_assumption_a_target_bound": (
            "sum_spatial_e osc_e(F o Q_hp_{ell,k})^2 <= C_Q * Lip(F)^2"
        ),
        "anisotropic_assumption_a_sum_domain": "spatial_links_only",
        "spatial_only_blocking_map_q_hp_constructed": False,
        "temporal_links_excluded_from_blocking": False,
        "balaban_cmp98_averaging_lipschitz_authority_cited": True,
        "balaban_cmp98_averaging_lipschitz_formalized_in_repo": False,
        "sprint81_qhp_local_oscillation_attempt_recorded": True,
        "formal_oscillation_seminorm_for_gauge_links": False,
        "formal_qhp_blocking_map_definition": False,
        "balaban_cmp98_averaging_locality_imported": False,
        "qhp_per_link_influence_cone_l_minus_2k": False,
        "qhp_local_oscillation_route_decision": (
            "BALABAN_CMP98_QHP_LOCAL_OSCILLATION_MISSING_FORMAL_LAYER"
        ),
        "sprint81a_authority_assembly_recorded": True,
        "balaban_cmp98_authority_accepted": True,
        "balaban_cmp98_local_oscillation_bound_for_qhp_authority_dependent": True,
        "balaban_cmp98_local_oscillation_bound_for_qhp_proved_in_repo": False,
        "lipschitz_to_squared_oscillation_for_qhp_authority_conditional": True,
        "anisotropic_assumption_a_authority_conditional": True,
        "anisotropic_assumption_a_unconditional_in_repo": False,
        "fixed_finite_volume_blocked_uv_closure_authority_conditional": True,
        "fixed_finite_volume_blocked_uv_closure_promoted_unconditionally": False,
        "sprint81b_support_interface_recorded": True,
        "support_interface_defined": True,
        "balaban_effective_action_carrier_defined": True,
        "polymer_carrier_defined": True,
        "polymer_in_relation_defined": True,
        "link_kind_temporal_spatial_defined": True,
        "temporal_link_predicate_defined": True,
        "spatial_link_predicate_defined": True,
        "polymer_support_defined": True,
        "spatial_support_predicate_defined": True,
        "residual_effective_action_term_defined": True,
        "activity_depends_only_on_links_inside_polymer_defined": True,
        "temporal_measure_factorization_lambda_one_reconciled": True,
        "defined_on_blocked_l2_spatial_graph_defined": True,
        "balaban_cmp98_local_oscillation_bound_for_qhp": False,
        "lipschitz_to_squared_oscillation_for_qhp": False,
        "squared_oscillation_summability": False,
        "squared_oscillation_summability_bound_proved": False,
        "sprint80_anisotropic_assumption_a_proof_plan_recorded": True,
        "sprint80_anisotropic_volume_arithmetic_closes_conditionally": True,
        "half_plane_blocking_map": "Q_hp",
        "isotropic_spacetime_link_dimension": ISOTROPIC_SPACETIME_LINK_DIMENSION,
        "anisotropic_spatial_link_multiplicity": ANISOTROPIC_SPATIAL_LINK_MULTIPLICITY,
        "isotropic_link_count_form": ISOTROPIC_LINK_COUNT_FORM,
        "anisotropic_spatial_link_count_form": ANISOTROPIC_LINK_COUNT_FORM,
        "isotropic_link_count_scaling_baseline": ISOTROPIC_LINK_COUNT_FORM,
        "anisotropic_spatial_link_count_scaling": ANISOTROPIC_LINK_COUNT_FORM,
        "oscillation_decay_form": OSCILLATION_DECAY_FORM,
        "oscillation_decay_scaling": OSCILLATION_DECAY_FORM,
        "anisotropic_uv_balance_form": ANISOTROPIC_UV_VOLUME_BALANCE,
        "anisotropic_assumption_a_conditional_volume_factor": "L^(-k)",
        "blocked_observable_continuum_limit_fixed_volume_promoted": False,
        "published_architecture_blocker": (
            "Assumption A for half-plane/spatial-only Balaban blocking"
        ),
        "uv_closure_lane_status": (
            "ANISOTROPIC_ASSUMPTION_A_AUTHORITY_CONDITIONAL"
        ),
        "current_uv_route_decision": (
            "ANISOTROPIC_ASSUMPTION_A_AUTHORITY_CONDITIONAL"
        ),
        "nc_absorption_floor_authority_cited": True,
        "nc_absorption_floor_authority_assumed": True,
        "nc_absorption_floor_authority_proved": False,
        "effective_action_polymers_spatial_only_for_a1": False,
        "polymer_defined_on_blocked_lattice": False,
        "polymer_defined_on_blocked_lattice_authority_conditional": True,
        "kp_entropy_at_blocked_scale_l2": False,
        "kp_entropy_at_blocked_scale_l2_authority_conditional": True,
        "eta4_earned_authority_conditional": True,
        "eta4_earned_unconditional": True,
        "temporal_entropy_quotient_halves_generic_4d_count": False,
        "all_diameter_weighted_kp": False,
        "all_diameter_weighted_kp_authority_conditional": True,
        "small_field_survival_provider_authority_available": True,
        "small_field_survival_provider_derived_in_repo": False,
        "small_field_spatial_blocking_compatibility_derived_in_repo": True,
        "polymer_activity_bound_preservation_derived_from_strong_kp": True,
        "small_field_strong_kp_input_derived_in_repo": True,
        "balaban_small_field_authority_split": True,
        "balaban_small_field_authority_split_into_four_analytic_lemmas": True,
        "balaban_small_field_bounds_derived_in_repo": False,
        "gauge_orbit_measure_authority_split": True,
        "gauge_orbit_measure_authority_split_into_three_analytic_lemmas": True,
        "gauge_orbit_measure_preservation_derived_in_repo": False,
        "temporal_transfer_compatibility_derived_in_repo": True,
        "carrier_balaban_small_field_bookkeeping_available": True,
        "carrier_balaban_analytic_decay_theorem_derived_in_repo": False,
        "carrier_gauge_fixing_continuum_slice_constructed_in_repo": False,
        "carrier_measure_continuum_gauge_measure_constructed_in_repo": False,
        "small_field_bounds_survive_anisotropic_blocking": False,
        "small_field_bounds_survive_anisotropic_blocking_authority_conditional": True,
        "lattice_mass_gap_provider_authority_available": True,
        "lattice_mass_gap_provider_derived_in_repo": False,
        "lattice_mass_gap_provider_split_into_four_analytic_lemmas": True,
        "next_required_lattice_mass_gap_inputs": [
            "TemporalTransferMatrixSpatialBlockingCompatibility",
            "TransferReflectionPositivity",
            "TransferSpectralGap",
            "PositiveLatticeMassGapExtraction",
        ],
        "temporal_transfer_matrix_compatible_with_spatial_blocking_authority_conditional": True,
        "transfer_spectral_gap_authority_conditional": True,
        "lattice_mass_gap_from_anisotropic_kp": False,
        "lattice_mass_gap_from_anisotropic_kp_authority_conditional": True,
        "thermodynamic_limit_provider_authority_available": True,
        "thermodynamic_limit_provider_derived_in_repo": False,
        "thermodynamic_limit_provider_split_into_five_analytic_lemmas": True,
        "next_required_thermodynamic_limit_inputs": [
            "UniformLatticeMassGap",
            "FiniteVolumeTightness",
            "InfiniteVolumeThermodynamicLimit",
            "ContinuumLimitExists",
            "Nontrivial4DSU3YangMillsMeasure",
        ],
        "uniform_lattice_mass_gap_authority_conditional": True,
        "thermodynamic_limit": False,
        "thermodynamic_limit_authority_conditional": True,
        "continuum_limit_exists_authority_conditional": True,
        "nontrivial_4d_su3_yang_mills_measure_authority_conditional": True,
        "os_axioms_provider_authority_available": True,
        "os_axioms_provider_derived_in_repo": False,
        "os_axioms_provider_split_into_five_analytic_lemmas": True,
        "next_required_os_axioms_inputs": [
            "ReflectionPositivity",
            "EuclideanCovariance",
            "OSSymmetry",
            "OSRegularity",
            "OSClustering",
        ],
        "reflection_positivity_authority_conditional": True,
        "osterwalder_schrader_axioms": False,
        "osterwalder_schrader_axioms_authority_conditional": True,
        "os_wightman_reconstruction_provider_authority_available": True,
        "os_wightman_reconstruction_provider_derived_in_repo": False,
        "os_wightman_reconstruction": False,
        "os_wightman_reconstruction_authority_conditional": True,
        "wightman_qft_authority_conditional": True,
        "continuum_mass_gap_transfer_provider_authority_available": True,
        "continuum_mass_gap_transfer_provider_derived_in_repo": False,
        "continuum_mass_gap_transfer_provider_split_into_four_analytic_lemmas": True,
        "next_required_continuum_mass_gap_transfer_inputs": [
            "UniformGapLowerBoundTransfer",
            "SpectralConvergence",
            "ContinuumTwoPointDecay",
            "PositiveContinuumMassGapExtraction",
        ],
        "continuum_mass_gap_transfer": False,
        "continuum_mass_gap_transfer_authority_conditional": True,
        "positive_continuum_mass_gap_authority_conditional": True,
        "mass_gap_survival_provider_authority_available": True,
        "mass_gap_survival_provider_derived_in_repo": False,
        "mass_gap_survival": False,
        "mass_gap_survival_authority_conditional": True,
        "clay_yang_mills_candidate_authority_conditional": True,
        "clay_yang_mills_promotion_boundary_defined": True,
        "all_providers_derived_in_repo": False,
        "clay_statement_boundary_discharged": False,
        "clay_yang_mills_promoted_authority_conditional": False,
        "positive_lattice_mass_gap": False,
        "positive_continuum_mass_gap": False,
        "wightman_qft": False,
        "clay_yang_mills_promoted": False,
        "current_route_decision": ROUTE_STRONG_KP_CLOSED,
        "target_route_state": "KP_GRAPH_IS_BLOCKED_L2_ETA4_CONFIRMED",
        "current_blocker": (
            "Authority route has AnisotropicAssumptionA conditional on CMP98; "
            "typed support interface, spatial-only assembly bridge, and "
            "Sprint 82 residual-support core/provider layers are defined and "
            "Balaban provider instances are available as authority assumptions; "
            "the authority-conditional KP path has now earned eta=4 and "
            "all-diameter KP; small-field survival, lattice mass gap, and "
            "thermodynamic/continuum limit, OS axioms, Wightman reconstruction, continuum mass-gap transfer, and mass-gap survival are now authority-conditional; the Clay promotion boundary is defined fail-closed; "
            "the unconditional path now has a direct strong Gate-B to KP path; "
            "sector-tagged action terms derive transfer/residual disjointness, "
            "and strong residual membership assembles spatial support directly, "
            "so eta=4/KP are no longer blocked by Gate B; "
            "unconditional CMP98 derivation still lacks "
            "Q_hp/osc_e formal layer"
        ),
        "next_required_lemma": "SmallFieldBoundsSurviveAnisotropicBlocking",
        "next_required_lemma_authority_conditional": (
            "BalabanSmallFieldRegionStability + "
            "BalabanFluctuationCovarianceBound + "
            "BalabanPolymerActivityExponentialDecay + "
            "BalabanScaleUniformConstants + "
            "GaugeFixingJacobianBound + GaugeOrbitVolumeUniform"
        ),
        "next_required_small_field_inputs": [
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
        "next_required_lemmas": next_required_lemmas,
        "next_required_unconditional_uv_lemmas": [
            "FormalOscillationSeminormForGaugeLinks",
            "FormalQhpBlockingMapDefinition",
            "BalabanCMP98AveragingLocalityImported",
            "QhpPerLinkInfluenceConeLMinus2k",
            "BalabanCMP98LocalOscillationBoundForQhp",
            "LipschitzToSquaredOscillationForQhp",
            "AnisotropicAssumptionA",
            "SquaredOscillationSummabilityForHalfPlaneBlocking",
        ],
        "complete_condition": (
            "all residual rows spatial_support_only=true, "
            "blocked_lattice_polymer=true, kp_entropy_used=4"
        ),
        "complete": False,
        "lemma_status": {
            "ResidualEffectiveActionSpatialSupportEvidence": "open",
            "TemporalTermAbsorbedNotResidualEvidence": "open",
            "TemporalLinkUseClassifiesTemporalTerm": "defined",
            "ResidualPolymerTermSupportSemantics": "conditional_on_resolver",
            "TemporalTransferResidualDisjointnessProvider": "authority_assumed",
            "PolymerInResidualTermResolver": "authority_assumed",
            "YMProviderDerivationInRepo": "defined",
            "YMProviderSemanticObligations": "defined",
            "YMTemporalTransferSemanticBridge": "defined",
            "YMResolvedMembershipSemantics": "defined",
            "YMGateBPackagingResolutionBoundary": "defined_fail_closed",
            "YMGateBPackagingResolutionAuthority": "authority_conditional",
            "YMGateBInRepoDerivationAttempts": "sector_disjointness_derived",
            "YMStrongGateBCarriers": "strong_path_defined",
            "YMStrongGateBKP": "strong_kp_closed",
            "ProvideGateBPackagingResolutionEvidence": "authority_conditional",
            "ProviderDerivationConstructors": "defined",
            "DeriveTypedTemporalTransferInterpretation": "proved_from_sector_partition",
            "StrengthenActionTermWithTransferResidualDisjointness": "strong_carrier_defined",
            "ReplaceWeakPolymerInWithStrongResidualMembership": "strong_membership_defined",
            "BridgeStrongGateBToLegacyWeakGate": "not_proof_critical",
            "RefactorEffectiveActionPolymersSpatialOnlyForA1ToStrongMembership": "not_proof_critical",
            "RefactorPolymerDefinedOnBlockedLatticeToStrongMembership": "not_proof_critical",
            "ProvePolymerInRefinesToStrongResidualMembership": (
                "refuted_for_current_weak_polymer_in"
            ),
            "ProveTemporalAbsorptionSemantics": "proved_from_current_constructors",
            "ProveTransferResidualExclusionSemantics": "proved_from_sector_partition",
            "ProveEveryPolymerInHasResolvedResidualTerm": "open",
            "ProveTemporalTransferResidualDisjointnessSemantics": "open",
            "ProveResidualMembershipSemantics": "open",
            "DeriveTemporalTransferResidualDisjointnessProviderInRepo": (
                "defined_conditional_on_semantics"
            ),
            "DerivePolymerInResidualTermResolverInRepo": (
                "defined_conditional_on_semantics"
            ),
            "YMResidualTermMembershipResolver": "defined",
            "YMResidualSupportEvidenceProvider": "defined",
            "YMResidualSupportBalabanAuthority": "authority_conditional",
            "ResidualTermHasNoTemporalSupportEvidence": "conditional_assembly_defined",
            "YMResidualSpatialSupportCore": "defined",
            "EffectiveActionPolymersSpatialOnlyForA1": "strong_path_closed",
            "YMEffectiveActionSpatialOnlyBridge": "defined",
            "BalabanEffectiveAction": "defined",
            "Polymer": "defined",
            "PolymerIn": "defined",
            "LinkKindTemporalSpatial": "defined",
            "TemporalLink": "defined",
            "SpatialLink": "defined",
            "PolymerSupport": "defined",
            "SpatialSupport": "defined",
            "ResidualEffectiveActionTerm": "defined",
            "ActivityDependsOnlyOnLinksInsidePolymer": "defined",
            "TemporalMeasureFactorizationLambdaOneReconciled": "defined",
            "DefinedOnBlockedL2SpatialGraph": "defined",
            "FormalOscillationSeminormForGaugeLinks": "open",
            "FormalQhpBlockingMapDefinition": "open",
            "BalabanCMP98AveragingLocalityImported": "open",
            "QhpPerLinkInfluenceConeLMinus2k": "open",
            "BalabanCMP98LocalOscillationBoundForQhp": "open",
            "LipschitzToSquaredOscillationForQhp": "authority_conditional",
            "AnisotropicAssumptionA": "authority_conditional",
            "SquaredOscillationSummabilityForHalfPlaneBlocking": "open",
            "FixedVolumeBlockedObservableContinuumLimit": "blocked",
            "YMBlockedL2KPEntropy": "strong_path_closed",
            "PolymerDefinedOnBlockedLattice": "strong_path_closed",
            "KPEntropyAtBlockedScaleL2": "strong_path_closed",
            "TemporalEntropyQuotientHalvesGeneric4DCount": "blocked",
            "AnisotropicL2WeightedKPCloses": "strong_path_closed",
            "AllDiameterWeightedKP": "strong_path_closed",
            "YMSmallFieldSurvivalAuthority": "authority_conditional",
            "SmallFieldBoundsSurviveAnisotropicBlocking": "authority_conditional_on_two_analytic_authorities",
            "SpatialOnlyBlockingCompatibility": "derived_in_repo",
            "TemporalTransferCompatibility": "derived_in_repo",
            "PolymerActivityBoundPreservation": "derived_from_strong_kp",
            "BalabanSmallFieldAuthority": "external_analytic_authority",
            "GaugeOrbitMeasureAuthority": "external_analytic_authority",
            "YMLatticeMassGapAuthority": "authority_conditional",
            "TemporalTransferMatrixCompatibleWithSpatialBlocking": "authority_conditional",
            "TransferSpectralGap": "authority_conditional",
            "LatticeMassGapFromAnisotropicKP": "authority_conditional",
            "YMThermodynamicLimitAuthority": "authority_conditional",
            "UniformLatticeMassGap": "authority_conditional",
            "ThermodynamicLimit": "authority_conditional",
            "ContinuumLimitExists": "authority_conditional",
            "Nontrivial4DSU3YangMillsMeasure": "authority_conditional",
            "YMOSAxiomsAuthority": "authority_conditional",
            "ReflectionPositivity": "authority_conditional",
            "OsterwalderSchraderAxioms": "authority_conditional",
            "YMOSWightmanReconstructionAuthority": "authority_conditional",
            "OSWightmanReconstruction": "authority_conditional",
            "WightmanQFT": "authority_conditional",
            "YMContinuumMassGapTransferAuthority": "authority_conditional",
            "ContinuumMassGapTransfer": "authority_conditional",
            "PositiveContinuumMassGap": "authority_conditional",
            "YMMassGapSurvivalAuthority": "authority_conditional",
            "MassGapSurvival": "authority_conditional",
            "ClayYangMillsCandidate": "authority_conditional",
            "YMClayPromotionBoundary": "defined_fail_closed",
            "ClayYangMillsPromotionBoundary": "defined_fail_closed",
            "DeriveProviderInstancesInRepo": "open",
            "ClayYangMills": "blocked",
        },
    }


def roadmap_status_payload() -> dict[str, Any]:
    return {
        "sprint": 79,
        "current_route_state": ROUTE_STRONG_KP_CLOSED,
        "current_uv_route_state": ROUTE_UV_BLOCKED,
        "current_uv_authority_route_state": (
            "ANISOTROPIC_ASSUMPTION_A_AUTHORITY_CONDITIONAL"
        ),
        "current_uv_blocker": (
            "Q_hp half-plane/spatial-only Balaban blocking lacks formal "
            "osc_e, Q_hp, CMP98 locality, and per-link influence-cone objects"
        ),
        "target_route_state": "KP_GRAPH_IS_BLOCKED_L2_ETA4_CONFIRMED",
        "current_blocker": (
            "Authority route has AnisotropicAssumptionA conditional on CMP98; "
            "typed support interface, spatial-only assembly bridge, and "
            "Sprint 82 residual-support core/provider layers are defined and "
            "Balaban provider instances are available as authority assumptions; "
            "authority-conditional path has eta=4/all-diameter KP/small-field "
            "survival/lattice mass gap/thermodynamic limit/OS axioms/Wightman "
            "reconstruction/continuum transfer/mass-gap survival and has a "
            "fail-closed Clay promotion boundary; provider constructors are "
            "implemented; sector-tagged action terms derive transfer/residual "
            "disjointness, strong Gate-B carriers assemble spatial support "
            "directly, and the direct strong Gate-B to KP path closes eta=4. "
            "The next blockers are downstream constructive-QFT gates"
        ),
        "next_required_lemmas": [
            "SmallFieldBoundsSurviveAnisotropicBlocking",
            "LatticeMassGapFromAnisotropicKP",
            "ThermodynamicLimit",
            "OsterwalderSchraderAxioms",
            "OSWightmanReconstruction",
            "ContinuumMassGapTransfer",
            "MassGapSurvival",
        ],
        "next_required_lemma": "SmallFieldBoundsSurviveAnisotropicBlocking",
        "next_required_lemmas_authority_conditional": [
            "DeriveProviderInstancesInRepo",
        ],
        "next_required_lemma_authority_conditional": "DeriveProviderInstancesInRepo",
        "next_required_uv_lemmas": [
            "SpatialOnlyBlockingMapQhp",
            "TemporalLinksExcludedFromBlocking",
            "BalabanAveragingMapLipschitzCMP98",
            "FormalOscillationSeminormForGaugeLinks",
            "FormalQhpBlockingMapDefinition",
            "BalabanCMP98AveragingLocalityImported",
            "QhpPerLinkInfluenceConeLMinus2k",
            "BalabanCMP98LocalOscillationBoundForQhp",
            "LipschitzToSquaredOscillationForQhp",
            "AnisotropicSquaredOscillationSummability",
            "AnisotropicAssumptionA",
        ],
        "complete_condition": (
            "all residual rows spatial_support_only=true, "
            "blocked_lattice_polymer=true, kp_entropy_used=4"
        ),
        "uv_complete_condition": (
            "squared-oscillation summability bound proved for Q_hp over "
            "spatial links only"
        ),
        "uv_complete": False,
        "complete": False,
    }


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=GATE_FIELDS)
        writer.writeheader()
        writer.writerows(rows)


def main() -> int:
    args = parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    write_csv(
        args.out_dir / "ym_sprint79_current_to_complete_gate_table.csv",
        gate_rows(),
    )
    (args.out_dir / "ym_sprint79_current_to_complete_summary.json").write_text(
        json.dumps(summary_payload(), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (args.out_dir / "ym_sprint79_roadmap_status.json").write_text(
        json.dumps(roadmap_status_payload(), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
