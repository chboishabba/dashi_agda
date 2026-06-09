from __future__ import annotations

import csv
import json
import math
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "ym_sprint79_current_to_complete_roadmap.py"

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


def run_roadmap(out_dir: Path) -> dict[str, Any]:
    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--out-dir",
            str(out_dir),
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return json.loads(
        (out_dir / "ym_sprint79_current_to_complete_summary.json").read_text()
    )


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def test_current_to_complete_outputs_and_schema(tmp_path: Path) -> None:
    out_dir = tmp_path / "roadmap"
    summary = run_roadmap(out_dir)

    gate_path = out_dir / "ym_sprint79_current_to_complete_gate_table.csv"
    status_path = out_dir / "ym_sprint79_roadmap_status.json"

    assert gate_path.exists()
    assert status_path.exists()
    assert summary["gate_table"] == gate_path.name
    assert summary["roadmap_status"] == status_path.name

    rows = read_csv(gate_path)
    assert rows
    assert list(rows[0].keys()) == GATE_FIELDS
    assert rows[0]["gate_name"] == "NcAbsorptionFloorAuthority"
    assert any(
        row["gate_name"] == "EffectiveActionPolymersSpatialOnlyForA1"
        for row in rows
    )
    assert any(row["gate_name"] == "PublishedArchitecture26020077" for row in rows)
    assert any(
        row["gate_name"] == "BalabanCMP98LocalOscillationBoundForQhp"
        for row in rows
    )
    assert any(
        row["gate_name"] == "LipschitzToSquaredOscillationForQhp"
        for row in rows
    )
    assert any(row["gate_name"] == "AnisotropicAssumptionA" for row in rows)
    assert any(
        row["gate_name"] == "SquaredOscillationSummabilityForHalfPlaneBlocking"
        for row in rows
    )
    assert any(row["gate_name"] == "ClayYangMills" for row in rows)


def test_current_to_complete_constants_and_guardrails(tmp_path: Path) -> None:
    summary = run_roadmap(tmp_path / "roadmap")

    assert summary["q_current"] == 0.23178189475262734
    assert math.isclose(summary["eta_blocked_l2_q"], 0.9271275790105094)
    assert math.isclose(summary["eta_blocked_l2_margin"], 0.07287242098949065)
    assert math.isclose(
        summary["eta_fine_lattice_spatial_q"], 1.390691368515764
    )
    assert math.isclose(
        summary["eta_fine_lattice_spatial_overshoot"], 0.390691368515764
    )
    assert math.isclose(summary["eta_generic_4d_q"], 1.8542551580210187)
    assert math.isclose(summary["eta_generic_4d_overshoot"], 0.8542551580210187)
    assert math.isclose(summary["eta6_q_threshold"], 1 / 6)
    assert math.isclose(
        summary["eta6_q_reduction_needed_percent"], 28.093319435263
    )
    assert summary["isotropic_link_count_form"] == "4*L^(4k)"
    assert summary["anisotropic_spatial_link_count_form"] == "3*L^(3k)"
    assert summary["oscillation_decay_form"] == "L^(-4k)"
    assert summary["anisotropic_uv_balance_form"] == "L^(-4k)*3*L^(3k)=3*L^(-k)"


def test_current_to_complete_fail_closed_status(tmp_path: Path) -> None:
    out_dir = tmp_path / "roadmap"
    summary = run_roadmap(out_dir)
    rows = read_csv(out_dir / "ym_sprint79_current_to_complete_gate_table.csv")
    status = json.loads((out_dir / "ym_sprint79_roadmap_status.json").read_text())

    assert summary["nc_absorption_floor_authority_cited"] is True
    assert summary["published_uv_closure_architecture_2602_0077_recorded"] is True
    assert summary["eriksson_2602_0077_theorem_1_6_conditional"] is True
    assert summary["eriksson_2602_0077_open_assumption"] == "AssumptionA"
    assert (
        summary["eriksson_2602_0077_theorem_1_6_status"]
        == "CONDITIONAL_ON_ASSUMPTION_A"
    )
    assert summary["polymer_representation_a1_is_not_open_assumption_a"] is True
    assert summary["anisotropic_assumption_a"] is False
    assert summary["anisotropic_assumption_a_fail_closed"] is True
    assert summary["sprint80_anisotropic_assumption_a_proof_plan_recorded"] is True
    assert summary["sprint80_anisotropic_volume_arithmetic_closes_conditionally"] is True
    assert summary["sprint81_qhp_local_oscillation_attempt_recorded"] is True
    assert summary["formal_oscillation_seminorm_for_gauge_links"] is False
    assert summary["formal_qhp_blocking_map_definition"] is False
    assert summary["balaban_cmp98_averaging_locality_imported"] is False
    assert summary["qhp_per_link_influence_cone_l_minus_2k"] is False
    assert summary["qhp_local_oscillation_route_decision"] == (
        "BALABAN_CMP98_QHP_LOCAL_OSCILLATION_MISSING_FORMAL_LAYER"
    )
    assert summary["sprint81a_authority_assembly_recorded"] is True
    assert summary["balaban_cmp98_authority_accepted"] is True
    assert (
        summary["balaban_cmp98_local_oscillation_bound_for_qhp_authority_dependent"]
        is True
    )
    assert (
        summary["balaban_cmp98_local_oscillation_bound_for_qhp_proved_in_repo"]
        is False
    )
    assert (
        summary["lipschitz_to_squared_oscillation_for_qhp_authority_conditional"]
        is True
    )
    assert summary["anisotropic_assumption_a_authority_conditional"] is True
    assert summary["anisotropic_assumption_a_unconditional_in_repo"] is False
    assert (
        summary["fixed_finite_volume_blocked_uv_closure_authority_conditional"]
        is True
    )
    assert (
        summary["fixed_finite_volume_blocked_uv_closure_promoted_unconditionally"]
        is False
    )
    assert summary["sprint81b_support_interface_recorded"] is True
    assert summary["support_interface_defined"] is True
    assert summary["lemma_status"]["YMEffectiveActionSpatialOnlyBridge"] == "defined"
    assert summary["lemma_status"]["YMResidualSpatialSupportCore"] == "defined"
    assert summary["lemma_status"]["YMResidualTermMembershipResolver"] == "defined"
    assert summary["lemma_status"]["YMResidualSupportEvidenceProvider"] == "defined"
    assert (
        summary["lemma_status"]["TemporalTransferResidualDisjointnessProvider"]
        == "authority_assumed"
    )
    assert summary["lemma_status"]["PolymerInResidualTermResolver"] == "authority_assumed"
    assert summary["lemma_status"]["YMProviderDerivationInRepo"] == "defined"
    assert summary["lemma_status"]["YMProviderSemanticObligations"] == "defined"
    assert summary["lemma_status"]["YMTemporalTransferSemanticBridge"] == "defined"
    assert summary["lemma_status"]["YMResolvedMembershipSemantics"] == "defined"
    assert (
        summary["lemma_status"]["YMGateBPackagingResolutionBoundary"]
        == "defined_fail_closed"
    )
    assert (
        summary["lemma_status"]["YMGateBPackagingResolutionAuthority"]
        == "authority_conditional"
    )
    assert (
        summary["lemma_status"]["ProvideGateBPackagingResolutionEvidence"]
        == "authority_conditional"
    )
    assert (
        summary["lemma_status"]["YMGateBInRepoDerivationAttempts"]
        == "sector_disjointness_derived"
    )
    assert summary["lemma_status"]["YMStrongGateBCarriers"] == "strong_path_defined"
    assert summary["lemma_status"]["YMStrongGateBKP"] == "strong_kp_closed"
    assert summary["lemma_status"]["ProviderDerivationConstructors"] == "defined"
    assert summary["lemma_status"]["DeriveTypedTemporalTransferInterpretation"] == (
        "proved_from_sector_partition"
    )
    assert (
        summary["lemma_status"]["StrengthenActionTermWithTransferResidualDisjointness"]
        == "strong_carrier_defined"
    )
    assert (
        summary["lemma_status"]["ReplaceWeakPolymerInWithStrongResidualMembership"]
        == "strong_membership_defined"
    )
    assert summary["lemma_status"]["BridgeStrongGateBToLegacyWeakGate"] == (
        "not_proof_critical"
    )
    assert (
        summary["lemma_status"][
            "RefactorEffectiveActionPolymersSpatialOnlyForA1ToStrongMembership"
        ]
        == "not_proof_critical"
    )
    assert (
        summary["lemma_status"]["RefactorPolymerDefinedOnBlockedLatticeToStrongMembership"]
        == "not_proof_critical"
    )
    assert (
        summary["lemma_status"]["ProvePolymerInRefinesToStrongResidualMembership"]
        == "refuted_for_current_weak_polymer_in"
    )
    assert summary["lemma_status"]["ProveTemporalAbsorptionSemantics"] == (
        "proved_from_current_constructors"
    )
    assert (
        summary["lemma_status"]["ProveTransferResidualExclusionSemantics"]
        == "proved_from_sector_partition"
    )
    assert (
        summary["lemma_status"]["ProveEveryPolymerInHasResolvedResidualTerm"]
        == "open"
    )
    assert (
        summary["lemma_status"]["ProveTemporalTransferResidualDisjointnessSemantics"]
        == "open"
    )
    assert summary["lemma_status"]["ProveResidualMembershipSemantics"] == "open"
    assert (
        summary["lemma_status"]["DeriveTemporalTransferResidualDisjointnessProviderInRepo"]
        == "defined_conditional_on_semantics"
    )
    assert summary["lemma_status"]["DerivePolymerInResidualTermResolverInRepo"] == (
        "defined_conditional_on_semantics"
    )
    assert (
        summary["lemma_status"]["YMResidualSupportBalabanAuthority"]
        == "authority_conditional"
    )
    assert summary["lemma_status"]["YMBlockedL2KPEntropy"] == "strong_path_closed"
    assert summary["lemma_status"]["PolymerDefinedOnBlockedLattice"] == (
        "strong_path_closed"
    )
    assert summary["lemma_status"]["KPEntropyAtBlockedScaleL2"] == (
        "strong_path_closed"
    )
    assert summary["lemma_status"]["AllDiameterWeightedKP"] == (
        "strong_path_closed"
    )
    assert (
        summary["lemma_status"]["ResidualTermHasNoTemporalSupportEvidence"]
        == "conditional_assembly_defined"
    )
    assert (
        summary["lemma_status"]["EffectiveActionPolymersSpatialOnlyForA1"]
        == "strong_path_closed"
    )
    assert summary["balaban_effective_action_carrier_defined"] is True
    assert summary["polymer_carrier_defined"] is True
    assert summary["polymer_in_relation_defined"] is True
    assert summary["spatial_support_predicate_defined"] is True
    assert summary["balaban_cmp98_local_oscillation_bound_for_qhp"] is False
    assert summary["lipschitz_to_squared_oscillation_for_qhp"] is False
    assert summary["squared_oscillation_summability_bound_proved"] is False
    assert summary["current_uv_route_decision"] == (
        "ANISOTROPIC_ASSUMPTION_A_AUTHORITY_CONDITIONAL"
    )
    assert summary["nc_absorption_floor_authority_assumed"] is True
    assert summary["nc_absorption_floor_authority_proved"] is False
    assert summary["effective_action_polymers_spatial_only_for_a1"] is False
    assert summary["polymer_defined_on_blocked_lattice"] is False
    assert summary["kp_entropy_at_blocked_scale_l2"] is False
    assert summary["temporal_entropy_quotient_halves_generic_4d_count"] is False
    assert summary["all_diameter_weighted_kp"] is False
    assert summary["small_field_survival_provider_authority_available"] is True
    assert summary["small_field_survival_provider_derived_in_repo"] is False
    assert summary["small_field_spatial_blocking_compatibility_derived_in_repo"] is True
    assert summary["polymer_activity_bound_preservation_derived_from_strong_kp"] is True
    assert summary["small_field_strong_kp_input_derived_in_repo"] is True
    assert summary["balaban_small_field_authority_split"] is True
    assert summary["balaban_small_field_bounds_derived_in_repo"] is False
    assert summary["gauge_orbit_measure_authority_split"] is True
    assert summary["gauge_orbit_measure_preservation_derived_in_repo"] is False
    assert summary["temporal_transfer_compatibility_derived_in_repo"] is True
    assert summary["small_field_bounds_survive_anisotropic_blocking"] is False
    assert (
        summary["small_field_bounds_survive_anisotropic_blocking_authority_conditional"]
        is True
    )
    assert summary["lattice_mass_gap_provider_authority_available"] is True
    assert summary["lattice_mass_gap_provider_derived_in_repo"] is True
    assert summary["lattice_mass_gap_provider_split_into_four_analytic_lemmas"] is True
    assert summary["next_required_lattice_mass_gap_inputs"] == []
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
    assert summary["thermodynamic_limit_provider_derived_in_repo"] is False
    assert summary["thermodynamic_limit_provider_split_into_five_analytic_lemmas"] is True
    assert summary["next_required_thermodynamic_limit_inputs"] == [
        "UniformLatticeMassGap",
        "FiniteVolumeTightness",
        "InfiniteVolumeThermodynamicLimit",
        "ContinuumLimitExists",
        "Nontrivial4DSU3YangMillsMeasure",
    ]
    assert summary["uniform_lattice_mass_gap_authority_conditional"] is True
    assert summary["thermodynamic_limit"] is False
    assert summary["thermodynamic_limit_authority_conditional"] is True
    assert summary["continuum_limit_exists_authority_conditional"] is True
    assert summary["wc3_uniform_cluster_summability_derived_in_repo"] is False
    assert summary["continuum_mass_gap_from_wc_conditional"] is True
    assert (
        summary["nontrivial_4d_su3_yang_mills_measure_unconditional"]
        is False
    )
    assert (
        summary["nontrivial_4d_su3_yang_mills_measure_authority_conditional"]
        is True
    )
    assert summary["su_n_greater_than_2_extension_derived_in_repo"] is False
    assert summary["su_n_greater_than_2_extension_open"] is True
    assert summary["external_acceptance_token_present"] is False
    assert summary["continuum_wc_next_open_walls"] == [
        "WC3UniformClusterSummability",
        "NoSpectralPollutionUnderContinuumLimit",
        "LatticeGapSurvivesContinuumScaling",
        "Nontrivial4DSU3YangMillsMeasure",
        "SUNGreaterThan2Extension",
        "ClayStatementBoundaryDischarged",
        "ExternalAcceptanceToken",
    ]
    assert summary["os_axioms_provider_authority_available"] is True
    assert summary["os_axioms_provider_derived_in_repo"] is False
    assert summary["os_axioms_provider_split_into_five_analytic_lemmas"] is True
    assert summary["next_required_os_axioms_inputs"] == [
        "ReflectionPositivity",
        "EuclideanCovariance",
        "OSSymmetry",
        "OSRegularity",
        "OSClustering",
    ]
    assert summary["reflection_positivity_authority_conditional"] is True
    assert summary["osterwalder_schrader_axioms"] is False
    assert summary["osterwalder_schrader_axioms_authority_conditional"] is True
    assert summary["os_wightman_reconstruction_provider_authority_available"] is True
    assert summary["os_wightman_reconstruction_provider_derived_in_repo"] is False
    assert summary["os_wightman_reconstruction"] is False
    assert summary["os_wightman_reconstruction_authority_conditional"] is True
    assert summary["wightman_qft_authority_conditional"] is True
    assert summary["continuum_mass_gap_transfer_provider_authority_available"] is True
    assert summary["continuum_mass_gap_transfer_provider_derived_in_repo"] is False
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
    assert summary["continuum_mass_gap_transfer"] is False
    assert summary["continuum_mass_gap_transfer_authority_conditional"] is True
    assert summary["positive_continuum_mass_gap_authority_conditional"] is True
    assert summary["mass_gap_survival_provider_authority_available"] is True
    assert summary["mass_gap_survival_provider_derived_in_repo"] is False
    assert summary["mass_gap_survival"] is False
    assert summary["mass_gap_survival_authority_conditional"] is True
    assert summary["clay_yang_mills_candidate_authority_conditional"] is True
    assert summary["clay_yang_mills_promotion_boundary_defined"] is True
    assert summary["all_providers_derived_in_repo"] is False
    assert summary["clay_statement_boundary_discharged"] is False
    assert summary["clay_yang_mills_promoted_authority_conditional"] is False
    assert summary["clay_yang_mills_promoted"] is False
    assert summary["current_route_decision"] == (
        "STRONG_GATE_B_TO_KP_CLOSED_NEXT_BLOCKER_SMALL_FIELD_SURVIVAL"
    )
    assert summary["next_required_lemma"] == "SmallFieldBoundsSurviveAnisotropicBlocking"
    assert summary["next_required_lemma_authority_conditional"] == (
        "BalabanSmallFieldRegionStability + "
        "BalabanFluctuationCovarianceBound + "
        "BalabanPolymerActivityExponentialDecay + "
        "BalabanScaleUniformConstants + "
        "GaugeFixingJacobianBound + GaugeOrbitVolumeUniform"
    )
    assert summary["next_required_small_field_inputs"] == [
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
    assert summary["carrier_balaban_small_field_bookkeeping_available"] is True
    assert summary["carrier_balaban_analytic_decay_theorem_derived_in_repo"] is False
    assert summary["carrier_gauge_fixing_continuum_slice_constructed_in_repo"] is False
    assert summary["carrier_measure_continuum_gauge_measure_constructed_in_repo"] is False
    assert summary["eta4_earned_authority_conditional"] is True
    assert summary["eta4_earned_unconditional"] is True
    assert summary["complete"] is False
    assert "next_required_lemmas" in summary
    assert "complete_condition" in summary
    assert "current_blocker" in summary
    assert (
        summary["lemma_status"]["AnisotropicL2WeightedKPCloses"]
        == "strong_path_closed"
    )
    assert (
        summary["lemma_status"]["YMSmallFieldSurvivalAuthority"]
        == "authority_conditional"
    )
    assert (
        summary["lemma_status"]["SmallFieldBoundsSurviveAnisotropicBlocking"]
        == "authority_conditional_on_two_analytic_authorities"
    )
    assert (
        summary["lemma_status"]["YMLatticeMassGapAuthority"]
        == "scoped_authority_closed"
    )
    assert (
        summary["lemma_status"]["TemporalTransferMatrixCompatibleWithSpatialBlocking"]
        == "derived_in_repo"
    )
    assert summary["lemma_status"]["TransferSpectralGap"] == "scoped_authority_closed"
    assert (
        summary["lemma_status"]["LatticeMassGapFromAnisotropicKP"]
        == "scoped_authority_closed"
    )
    assert (
        summary["lemma_status"]["YMThermodynamicLimitAuthority"]
        == "authority_conditional"
    )
    assert summary["lemma_status"]["UniformLatticeMassGap"] == "authority_conditional"
    assert summary["lemma_status"]["ThermodynamicLimit"] == "authority_conditional"
    assert summary["lemma_status"]["ContinuumLimitExists"] == "authority_conditional"
    assert summary["lemma_status"]["WC3UniformClusterSummability"] == "open"
    assert (
        summary["lemma_status"]["NoSpectralPollutionUnderContinuumLimit"]
        == "conditional_on_wc3"
    )
    assert summary["lemma_status"]["ContinuumMassGapFromWC"] == "conditional_closed"
    assert (
        summary["lemma_status"]["Nontrivial4DSU3YangMillsMeasure"]
        == "authority_conditional"
    )
    assert summary["lemma_status"]["SUNGreaterThan2Extension"] == "open"
    assert (
        summary["lemma_status"]["YMOSAxiomsAuthority"]
        == "authority_conditional"
    )
    assert summary["lemma_status"]["ReflectionPositivity"] == "authority_conditional"
    assert (
        summary["lemma_status"]["OsterwalderSchraderAxioms"]
        == "authority_conditional"
    )
    assert (
        summary["lemma_status"]["YMOSWightmanReconstructionAuthority"]
        == "authority_conditional"
    )
    assert (
        summary["lemma_status"]["OSWightmanReconstruction"]
        == "authority_conditional"
    )
    assert summary["lemma_status"]["WightmanQFT"] == "authority_conditional"
    assert (
        summary["lemma_status"]["YMContinuumMassGapTransferAuthority"]
        == "authority_conditional"
    )
    assert (
        summary["lemma_status"]["ContinuumMassGapTransfer"]
        == "authority_conditional"
    )
    assert (
        summary["lemma_status"]["PositiveContinuumMassGap"]
        == "authority_conditional"
    )
    assert (
        summary["lemma_status"]["YMMassGapSurvivalAuthority"]
        == "authority_conditional"
    )
    assert summary["lemma_status"]["MassGapSurvival"] == "authority_conditional"
    assert (
        summary["lemma_status"]["ClayYangMillsCandidate"]
        == "authority_conditional"
    )
    assert (
        summary["lemma_status"]["YMClayPromotionBoundary"]
        == "defined_fail_closed"
    )
    assert (
        summary["lemma_status"]["ClayYangMillsPromotionBoundary"]
        == "defined_fail_closed"
    )
    assert summary["lemma_status"]["DeriveProviderInstancesInRepo"] == "open"

    assert status["current_route_state"] == (
        "STRONG_GATE_B_TO_KP_CLOSED_NEXT_BLOCKER_SMALL_FIELD_SURVIVAL"
    )
    assert status["current_uv_route_state"] == "ANISOTROPIC_ASSUMPTION_A_OPEN_FAIL_CLOSED"
    assert status["current_uv_authority_route_state"] == (
        "ANISOTROPIC_ASSUMPTION_A_AUTHORITY_CONDITIONAL"
    )
    assert status["complete"] is False
    assert status["uv_complete"] is False
    assert status["next_required_lemma"] == "SmallFieldBoundsSurviveAnisotropicBlocking"
    assert status["next_required_lemma_authority_conditional"] == (
        "DeriveProviderInstancesInRepo"
    )
    assert (
        status["next_required_lemmas"][0]
        == "SmallFieldBoundsSurviveAnisotropicBlocking"
    )
    assert status["next_required_uv_lemmas"][0] == "SpatialOnlyBlockingMapQhp"
    assert "FormalQhpBlockingMapDefinition" in status["next_required_uv_lemmas"]

    assert all(row["proved_in_repo"] == "False" for row in rows)
    assert any(
        row["route_decision"] == "ANISOTROPIC_KP_ROUTE_BLOCKED" for row in rows
    )
