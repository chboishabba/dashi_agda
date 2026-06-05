from __future__ import annotations

import csv
import json
import subprocess
import sys
from pathlib import Path


SCRIPT = Path("scripts/clay_sprint83_ym_ns_lane_status_audit.py")


def run_audit(tmp_path: Path) -> tuple[Path, dict]:
    out_dir = tmp_path / "clay_sprint83_ym_ns"
    subprocess.run(
        [sys.executable, str(SCRIPT), "--out-dir", str(out_dir)],
        check=True,
        cwd=Path.cwd(),
    )
    summary = json.loads(
        (out_dir / "clay_sprint83_ym_ns_lane_status_summary.json").read_text()
    )
    return out_dir, summary


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        return list(csv.DictReader(handle))


def test_combined_audit_outputs_and_schema(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)

    assert summary["contract"] == "clay_sprint83_ym_ns_lane_status_audit"
    assert (
        out_dir / "clay_sprint83_ym_ns_lane_source_surface_table.csv"
    ).exists()
    assert (out_dir / "clay_sprint83_ym_ns_lane_gate_table.csv").exists()
    assert (out_dir / "clay_sprint83_ym_ns_lane_status_summary.json").exists()

    source_rows = read_csv(out_dir / "clay_sprint83_ym_ns_lane_source_surface_table.csv")
    gate_rows = read_csv(out_dir / "clay_sprint83_ym_ns_lane_gate_table.csv")

    assert {row["surface_name"] for row in source_rows} == {
        "StrongGateBCarriers",
        "StrongGateBKP",
        "WeakPolymerInCounterexample",
        "SmallFieldSurvivalAuthority",
        "LatticeMassGapAuthority",
        "TemporalTransferSpatialBlockingCompatibilityReceipt",
        "BlockedActionTransferKernelSeparationReceipt",
        "ExactBlockedActionTransferResidualSumReceipt",
        "ContinuumMassGapTransferAuthority",
        "MassGapSurvivalAuthority",
        "ClayPromotionBoundary",
        "HminusHalfGateDecisionPivot",
        "KStarHHalfTailObstructionReceipt",
        "NonCircularKStarDriftBoundTarget",
        "TailRestrictedThetaDiagnostic",
        "ThetaTailToBKMBridge",
    }
    assert {row["gate_name"] for row in gate_rows} >= {
        "StrongGateBToKP",
        "WeakPolymerInCounterexample",
        "SmallFieldSurvivalAuthority",
        "LatticeMassGapAuthority",
        "TemporalTransferSpatialBlockingCompatibility",
        "ContinuumMassGapTransfer",
        "MassGapSurvival",
        "ClayYangMillsPromotionBoundary",
        "HminusHalfUniformAbsorptionGate",
        "NonCircularKStarDriftBound",
        "ThetaTailToBKMOrSerrinContinuation",
    }


def test_combined_audit_records_required_source_surfaces(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)
    source_rows = read_csv(out_dir / "clay_sprint83_ym_ns_lane_source_surface_table.csv")

    assert summary["ym_strong_gate_b_source_surface"] is True
    assert summary["ym_strong_gate_b_kp_source_surface"] is True
    assert summary["ym_weak_polymer_in_counterexample_source"] is True
    assert summary["ym_small_field_authority_surface"] is True
    assert summary["ym_lattice_mass_gap_authority_surface"] is True
    assert (
        summary["ym_temporal_transfer_spatial_blocking_decomposition_surface"]
        is True
    )
    assert summary["ym_blocked_action_transfer_kernel_separation_surface"] is True
    assert summary["ym_exact_blocked_action_transfer_residual_sum_surface"] is True
    assert summary["ym_continuum_mass_gap_transfer_authority_surface"] is True
    assert summary["ym_mass_gap_survival_authority_surface"] is True
    assert summary["ym_clay_promotion_boundary_surface"] is True
    assert summary["ns_hminus_source_surface"] is True
    assert summary["ns_kstar_hhalf_tail_obstruction_surface"] is True
    assert summary["ns_kstar_source_surface"] is True
    assert summary["ns_theta_source_surface"] is True
    assert summary["ns_bkm_source_surface"] is True
    assert summary["all_required_source_surfaces_present"] is True
    assert all(row["present_in_repo"] == "True" for row in source_rows)


def test_combined_audit_fails_closed_and_promotions_false(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)
    source_rows = read_csv(out_dir / "clay_sprint83_ym_ns_lane_source_surface_table.csv")
    gate_rows = read_csv(out_dir / "clay_sprint83_ym_ns_lane_gate_table.csv")

    assert summary["complete"] is False
    assert summary["route_decision"] == "CLAY_SPRINT83_YM_NS_OPEN_FAIL_CLOSED"
    assert summary["clay_yang_mills_promoted"] is False
    assert summary["clay_navier_stokes_promoted"] is False
    assert summary["clay_promotions_false"] is True
    assert all(row["clay_promotion"] == "False" for row in source_rows)
    assert all(row["clay_promotion"] == "False" for row in gate_rows)
    assert all(
        row["route_decision"] == "CLAY_SPRINT83_YM_NS_OPEN_FAIL_CLOSED"
        for row in source_rows + gate_rows
    )


def test_combined_audit_records_next_open_gates(tmp_path: Path) -> None:
    _out_dir, summary = run_audit(tmp_path)

    assert summary["next_required_ym_gate"] == "ClayYangMillsPromotionBoundary"
    assert summary["next_required_ns_gate"] == "HminusHalfUniformAbsorptionGate"
    assert summary["ym_small_field_survival_provider_authority_available"] is True
    assert summary["ym_small_field_survival_provider_derived_in_repo"] is True
    assert summary["ym_small_field_bounds_survive_unconditional"] is True
    assert summary["ym_lattice_mass_gap_provider_authority_available"] is True
    assert summary["ym_lattice_mass_gap_provider_derived_in_repo"] is False
    assert summary["ym_lattice_mass_gap_provider_imported_by_authority"] is True
    assert (
        summary["ym_lattice_mass_gap_provider_split_into_four_analytic_lemmas"]
        is True
    )
    assert summary["ym_lattice_mass_gap_provider_source_map_defined"] is True
    assert summary["ym_lattice_mass_gap_provider_source_map_surfaces"] == [
        "TemporalTransferMatrixSpatialBlockingCompatibility",
        "TransferReflectionPositivity",
        "TransferSpectralGap",
        "PositiveLatticeMassGapExtraction",
    ]
    assert summary["ym_temporal_transfer_spatial_blocking_sublemmas"] == [
        "SpatialBlockingPreservesTimeSlices",
        "SpatialBlockingPreservesTemporalBoundaryLinks",
        "BlockedActionSeparatesTransferKernel",
        "BalabanPartitionIdentityCommutesWithTemporalTrace",
        "TransferHilbertSpaceCompatibleWithSpatialBlocking",
    ]
    assert summary["ym_temporal_transfer_spatial_blocking_derived_sublemmas"] == [
        "SpatialBlockingPreservesTimeSlices",
        "SpatialBlockingPreservesTemporalBoundaryLinks",
    ]
    assert summary["ym_temporal_transfer_spatial_blocking_open_sublemmas"] == [
        "BlockedActionSeparatesTransferKernel",
        "BalabanPartitionIdentityCommutesWithTemporalTrace",
        "TransferHilbertSpaceCompatibleWithSpatialBlocking",
    ]
    assert summary["ym_blocked_action_transfer_kernel_required_inputs"] == [
        "ActionTermSectorTagComplete",
        "MixedPlaquettesAbsorbedIntoTransfer",
        "StrongTransferResidualDisjointness",
        "SpatialBlockingCreatesNoNewCrossTerms",
        "ExactBlockedActionTransferResidualSum",
    ]
    assert summary["ym_spatial_blocking_creates_no_new_cross_terms_derived_in_repo"] is True
    assert summary["ym_exact_blocked_action_transfer_residual_sum_required_inputs"] == [
        "BlockedActionTermEnumeration",
        "TransferKernelActionTermProjection",
        "SpatialResidualActionTermProjection",
        "TransferResidualProjectionDisjoint",
        "ProjectionUnionCoversBlockedAction",
        "ActionSumRespectsProjectionUnion",
    ]
    assert (
        summary["ym_blocked_action_transfer_kernel_next_gate"]
        == "ExactBlockedActionTransferResidualSum"
    )
    assert summary["ns_kstar_hhalf_tail_next_gate"] == "QhpTailSmallnessAtDangerShell"
    assert summary["ns_kstar_hhalf_tail_obstruction_recorded"] is True
    assert (
        summary[
            "ym_temporal_transfer_spatial_blocking_full_compatibility_derived_in_repo"
        ]
        is False
    )
    assert summary["ym_next_required_lattice_mass_gap_inputs"] == [
        "TemporalTransferMatrixSpatialBlockingCompatibility",
        "TransferReflectionPositivity",
        "TransferSpectralGap",
        "PositiveLatticeMassGapExtraction",
    ]
    assert (
        summary["ym_lattice_mass_gap_from_anisotropic_kp_authority_conditional"]
        is True
    )
    assert summary["ym_lattice_mass_gap_from_anisotropic_kp_unconditional"] is False
    assert summary["ym_continuum_mass_gap_transfer_provider_derived_in_repo"] is True
    assert summary["ym_mass_gap_survival_provider_derived_in_repo"] is True
    assert summary["ym_clay_statement_boundary_open_obligations"] == [
        "missingUnconditionalProviderDerivations",
        "missingConstructiveYangMillsExistence",
        "missingPhysicalHamiltonianMassGapIdentification",
        "missingClayStatementFormulationEquivalence",
        "missingExternalAcceptanceOrReviewReceipt",
    ]
    assert summary["ym_clay_statement_boundary_source_map_defined"] is True
    assert summary["ym_clay_statement_boundary_source_map_surfaces"] == [
        "ContinuumClayYMConstructiveBlockerThreadReceipt",
        "ColimitHamiltonianGapThreadReceipt",
        "YangMillsMassGapBoundaryReceipt",
        "YMConstructive5DRouteAuditReceipt",
    ]
    assert summary["ym_constructive_existence_source_still_blocked"] is True
    assert (
        summary["ym_physical_hamiltonian_gap_lift_source_still_blocked"]
        is True
    )
    assert (
        summary["ym_physical_stone_hamiltonian_identification_still_blocked"]
        is True
    )
    assert summary["ym_physical_stone_spectral_lower_bound_still_blocked"] is True
    assert summary["ym_external_constructive_route_still_blocked"] is True
    assert summary["ym_clay_statement_boundary_discharged"] is False
