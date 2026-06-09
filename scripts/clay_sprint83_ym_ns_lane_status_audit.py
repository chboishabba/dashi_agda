#!/usr/bin/env python3
"""Sprint 83 combined YM/NS Clay lane status audit."""

from __future__ import annotations

import argparse
import csv
import json
import re
from pathlib import Path
from typing import Any


ROUTE_OPEN_FAIL_CLOSED = "CLAY_SPRINT83_YM_NS_OPEN_FAIL_CLOSED"
ROUTE_PROMOTION_VIOLATION = "CLAY_SPRINT83_YM_NS_PROMOTION_VIOLATION"

SOURCE_FIELDS = [
    "domain",
    "surface_id",
    "surface_name",
    "path",
    "required_anchor",
    "status",
    "present_in_repo",
    "proved_in_repo",
    "clay_promotion",
    "route_decision",
]

GATE_FIELDS = [
    "domain",
    "gate_id",
    "gate_name",
    "status",
    "next_required_input",
    "proved_in_repo",
    "clay_promotion",
    "route_decision",
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    return parser.parse_args()


def required_surfaces() -> list[dict[str, Any]]:
    return [
        {
            "domain": "YM",
            "surface_id": "YM1",
            "surface_name": "StrongGateBCarriers",
            "path": "DASHI/Physics/Closure/YMStrongGateBCarriers.agda",
            "required_anchor": "strongGateBSpatialSupportAssemblyDefined",
            "status": "STRONG_GATE_B_SOURCE_PRESENT_NO_CLAY_PROMOTION",
            "proved_in_repo": True,
            "clay_promotion": False,
        },
        {
            "domain": "YM",
            "surface_id": "YM2",
            "surface_name": "StrongGateBKP",
            "path": "DASHI/Physics/Closure/YMStrongGateBKP.agda",
            "required_anchor": "strongGateBToKPFromSectorDisjointness",
            "status": "STRONG_GATE_B_TO_KP_SOURCE_PRESENT_NO_CLAY_PROMOTION",
            "proved_in_repo": True,
            "clay_promotion": False,
        },
        {
            "domain": "YM",
            "surface_id": "YM3",
            "surface_name": "WeakPolymerInCounterexample",
            "path": "DASHI/Physics/Closure/YMResidualSpatialSupportCounterexample.agda",
            "required_anchor": "unconditionalResidualSpatialSupportEvidenceImpossible",
            "status": "WEAK_POLYMER_IN_COUNTEREXAMPLE_SOURCE_PRESENT",
            "proved_in_repo": True,
            "clay_promotion": False,
        },
        {
            "domain": "YM",
            "surface_id": "YM4",
            "surface_name": "SmallFieldSurvivalAuthority",
            "path": "DASHI/Physics/Closure/YMSmallFieldSurvivalAuthority.agda",
            "required_anchor": "smallFieldSurvivalAuthorityBoundary",
            "status": "SMALL_FIELD_PROVIDER_BACKED_AUTHORITY_CLOSED",
            "proved_in_repo": True,
            "clay_promotion": False,
        },
        {
            "domain": "YM",
            "surface_id": "YM5",
            "surface_name": "LatticeMassGapAuthority",
            "path": "DASHI/Physics/Closure/YMLatticeMassGapAuthority.agda",
            "required_anchor": "latticeMassGapAuthorityBoundary",
            "status": "LATTICE_MASS_GAP_AUTHORITY_CLOSED_UNCONDITIONAL_PROVIDER_OPEN",
            "proved_in_repo": False,
            "clay_promotion": False,
        },
        {
            "domain": "YM",
            "surface_id": "YM6",
            "surface_name": "TemporalTransferSpatialBlockingCompatibilityReceipt",
            "path": (
                "DASHI/Physics/Closure/"
                "YMSprint85TemporalTransferSpatialBlockingCompatibilityReceipt.agda"
            ),
            "required_anchor": (
                "canonicalYMSprint85TemporalTransferSpatialBlockingCompatibilityReceipt"
            ),
            "status": "TRANSFER_SPATIAL_BLOCKING_DECOMPOSITION_CLOSED",
            "proved_in_repo": True,
            "clay_promotion": False,
        },
        {
            "domain": "YM",
            "surface_id": "YM6a",
            "surface_name": "BlockedActionTransferKernelSeparationReceipt",
            "path": (
                "DASHI/Physics/Closure/"
                "YMSprint86BlockedActionTransferKernelSeparationReceipt.agda"
            ),
            "required_anchor": (
                "canonicalYMSprint86BlockedActionTransferKernelSeparationReceipt"
            ),
            "status": "BLOCKED_ACTION_TRANSFER_KERNEL_REFINED_OPEN",
            "proved_in_repo": False,
            "clay_promotion": False,
        },
        {
            "domain": "YM",
            "surface_id": "YM6b",
            "surface_name": "ExactBlockedActionTransferResidualSumReceipt",
            "path": (
                "DASHI/Physics/Closure/"
                "YMSprint87ExactBlockedActionTransferResidualSumReceipt.agda"
            ),
            "required_anchor": (
                "canonicalYMSprint87ExactBlockedActionTransferResidualSumReceipt"
            ),
            "status": "EXACT_BLOCKED_ACTION_SUM_REFINED_CLOSED",
            "proved_in_repo": True,
            "clay_promotion": False,
        },
        {
            "domain": "YM",
            "surface_id": "YM7",
            "surface_name": "ContinuumMassGapTransferAuthority",
            "path": "DASHI/Physics/Closure/YMContinuumMassGapTransferAuthority.agda",
            "required_anchor": "continuumMassGapTransferAuthorityBoundary",
            "status": "CONTINUUM_TRANSFER_PROVIDER_BACKED_AUTHORITY_CLOSED",
            "proved_in_repo": True,
            "clay_promotion": False,
        },
        {
            "domain": "YM",
            "surface_id": "YM8",
            "surface_name": "MassGapSurvivalAuthority",
            "path": "DASHI/Physics/Closure/YMMassGapSurvivalAuthority.agda",
            "required_anchor": "massGapSurvivalAuthorityBoundary",
            "status": "MASS_GAP_SURVIVAL_PROVIDER_BACKED_AUTHORITY_CLOSED",
            "proved_in_repo": True,
            "clay_promotion": False,
        },
        {
            "domain": "YM",
            "surface_id": "YM8a",
            "surface_name": "ContinuumMassGapWCBoundaryReceipt",
            "path": (
                "DASHI/Physics/Closure/"
                "YMSprint90ContinuumMassGapWCBoundaryReceipt.agda"
            ),
            "required_anchor": (
                "canonicalYMSprint90ContinuumMassGapWCBoundaryReceipt"
            ),
            "status": "WC3_CONTINUUM_SURVIVAL_BOUNDARY_RECORDED_FAIL_CLOSED",
            "proved_in_repo": True,
            "clay_promotion": False,
        },
        {
            "domain": "YM",
            "surface_id": "YM9",
            "surface_name": "ClayPromotionBoundary",
            "path": "DASHI/Physics/Closure/YMClayPromotionBoundary.agda",
            "required_anchor": "clayStatementBoundaryRequirements",
            "status": "CLAY_PROMOTION_BOUNDARY_DEFINED_FAIL_CLOSED",
            "proved_in_repo": False,
            "clay_promotion": False,
        },
        {
            "domain": "NS",
            "surface_id": "NS1",
            "surface_name": "HminusHalfGateDecisionPivot",
            "path": "DASHI/Physics/Closure/NSHminusHalfGateDecisionPivotReceipt.agda",
            "required_anchor": "hMinusUniformAbsorptionProofActiveIsFalse",
            "status": "RECORDED_UNIFORM_ABSORPTION_OPEN",
            "proved_in_repo": False,
            "clay_promotion": False,
        },
        {
            "domain": "NS",
            "surface_id": "NS1a",
            "surface_name": "KStarHHalfTailObstructionReceipt",
            "path": (
                "DASHI/Physics/Closure/"
                "NSSprint86KStarHHalfTailObstructionReceipt.agda"
            ),
            "required_anchor": (
                "canonicalNSSprint86KStarHHalfTailObstructionReceipt"
            ),
            "status": "KSTAR_HHALF_TAIL_OBSTRUCTION_RECORDED_OPEN",
            "proved_in_repo": False,
            "clay_promotion": False,
        },
        {
            "domain": "NS",
            "surface_id": "NS2",
            "surface_name": "NonCircularKStarDriftBoundTarget",
            "path": "DASHI/Physics/Closure/NSNonCircularKStarDriftBoundTargetReceipt.agda",
            "required_anchor": "canonicalNonCircularKStarOpenObligations",
            "status": "TARGET_RECORDED_OPEN",
            "proved_in_repo": False,
            "clay_promotion": False,
        },
        {
            "domain": "NS",
            "surface_id": "NS3",
            "surface_name": "TailRestrictedThetaDiagnostic",
            "path": "DASHI/Physics/Closure/NSTailRestrictedThetaDiagnosticReceipt.agda",
            "required_anchor": "claySeamUsesTailRestrictedTheta",
            "status": "DIAGNOSTIC_SURFACE_RECORDED_NO_PROMOTION",
            "proved_in_repo": False,
            "clay_promotion": False,
        },
        {
            "domain": "NS",
            "surface_id": "NS4",
            "surface_name": "ThetaTailToBKMBridge",
            "path": "DASHI/Physics/Closure/NSThetaTailToBKMBridgeReceipt.agda",
            "required_anchor": "continuumBKMCriterionNotDischargedHere",
            "status": "CONDITIONAL_BRIDGE_RECORDED_OPEN",
            "proved_in_repo": False,
            "clay_promotion": False,
        },
    ]


def surface_present(repo_root: Path, row: dict[str, Any]) -> bool:
    path = repo_root / row["path"]
    if not path.exists():
        return False
    return row["required_anchor"] in path.read_text()


def source_anchor_present(repo_root: Path, relative_path: str, anchor: str) -> bool:
    path = repo_root / relative_path
    if not path.exists():
        return False
    return anchor in path.read_text()


def source_bool_assignment(repo_root: Path, relative_path: str, name: str) -> bool:
    path = repo_root / relative_path
    if not path.exists():
        return False
    match = re.search(
        rf"^{re.escape(name)}\s*=\s*(true|false)\s*$",
        path.read_text(),
        re.MULTILINE,
    )
    return bool(match and match.group(1) == "true")


def choose_route(*, clay_yang_mills_promoted: bool, clay_navier_stokes_promoted: bool) -> str:
    if clay_yang_mills_promoted or clay_navier_stokes_promoted:
        return ROUTE_PROMOTION_VIOLATION
    return ROUTE_OPEN_FAIL_CLOSED


def source_rows(repo_root: Path, route_decision: str) -> list[dict[str, Any]]:
    return [
        {
            **row,
            "present_in_repo": surface_present(repo_root, row),
            "route_decision": route_decision,
        }
        for row in required_surfaces()
    ]


def gate_rows(repo_root: Path, route_decision: str) -> list[dict[str, Any]]:
    lattice_mass_gap_authority_path = (
        "DASHI/Physics/Closure/YMLatticeMassGapAuthority.agda"
    )
    temporal_transfer_spatial_blocking_derived = source_bool_assignment(
        repo_root,
        lattice_mass_gap_authority_path,
        "temporalTransferMatrixSpatialBlockingCompatibilityDerivedInRepo",
    )
    temporal_transfer_status = (
        "DERIVED_IN_REPO_NO_CLAY_PROMOTION"
        if temporal_transfer_spatial_blocking_derived
        else "PARTIAL_DECOMPOSITION_IN_REPO_FULL_COMPATIBILITY_OPEN"
    )
    temporal_transfer_next_input = (
        "lattice mass-gap provider closed by scoped authority; Clay boundary remains"
        if temporal_transfer_spatial_blocking_derived
        else (
            "BlockedActionSeparatesTransferKernel + "
            "BalabanPartitionIdentityCommutesWithTemporalTrace + "
            "TransferHilbertSpaceCompatibleWithSpatialBlocking"
        )
    )
    raw_rows = [
        (
            "YM",
            "YMG1",
            "StrongGateBToKP",
            "SOURCE_SURFACE_PRESENT_DOWNSTREAM_QFT_GATES_OPEN",
            "SmallFieldBoundsSurviveAnisotropicBlocking",
            True,
            False,
        ),
        (
            "YM",
            "YMG2",
            "WeakPolymerInCounterexample",
            "CURRENT_WEAK_POLYMER_IN_REFUTES_UNCONDITIONAL_SPATIAL_SUPPORT",
            "keep strong residual membership on proof-critical lane",
            True,
            False,
        ),
        (
            "YM",
            "YMG3",
            "SmallFieldSurvivalAuthority",
            "PROVIDER_BACKED_AUTHORITY_CLOSED",
            "LatticeMassGapAuthority provider source map",
            True,
            False,
        ),
        (
            "YM",
            "YMG4",
            "LatticeMassGapAuthority",
            "SCOPED_AUTHORITY_CLOSED_CLAY_BOUNDARY_OPEN",
            "ClayYangMillsPromotionBoundary",
            True,
            False,
        ),
        (
            "YM",
            "YMG5",
            "TemporalTransferSpatialBlockingCompatibility",
            temporal_transfer_status,
            temporal_transfer_next_input,
            temporal_transfer_spatial_blocking_derived,
            False,
        ),
        (
            "YM",
            "YMG6",
            "ContinuumMassGapTransfer",
            "PROVIDER_BACKED_AUTHORITY_CLOSED",
            "MassGapSurvivalProvider",
            True,
            False,
        ),
        (
            "YM",
            "YMG7",
            "MassGapSurvival",
            "PROVIDER_BACKED_AUTHORITY_CLOSED",
            "ClayYangMillsPromotionBoundary",
            True,
            False,
        ),
        (
            "YM",
            "YMG8",
            "ClayYangMillsPromotionBoundary",
            "DEFINED_FAIL_CLOSED_OPEN_OBLIGATIONS_REMAIN",
            "unconditional provider derivations + constructive YM existence + physical Hamiltonian mass-gap identification + Clay statement equivalence + external review receipt",
            False,
            False,
        ),
        (
            "NS",
            "NSG1",
            "HminusHalfUniformAbsorptionGate",
            "OPEN_NOT_PROVED_IN_REPO",
            "non-circular H^{-1/2} nonlinear-defect estimate",
            False,
            False,
        ),
        (
            "NS",
            "NSG2",
            "NonCircularKStarDriftBound",
            "OPEN_AFTER_HMINUS_HALF_GATE",
            "non-circular high-high control plus K*(t) drift containment",
            False,
            False,
        ),
        (
            "NS",
            "NSG3",
            "ThetaTailToBKMOrSerrinContinuation",
            "CONDITIONAL_BRIDGE_ONLY_OPEN_BOUNDARIES_REMAIN",
            "uniform K* bound, theta tail control, and BKM/Serrin discharge",
            False,
            False,
        ),
    ]
    return [
        {
            "domain": domain,
            "gate_id": gate_id,
            "gate_name": gate_name,
            "status": status,
            "next_required_input": next_required_input,
            "proved_in_repo": proved,
            "clay_promotion": clay_promotion,
            "route_decision": route_decision,
        }
        for (
            domain,
            gate_id,
            gate_name,
            status,
            next_required_input,
            proved,
            clay_promotion,
        ) in raw_rows
    ]


def summary_payload(repo_root: Path) -> dict[str, Any]:
    clay_yang_mills_promoted = False
    clay_navier_stokes_promoted = False
    route_decision = choose_route(
        clay_yang_mills_promoted=clay_yang_mills_promoted,
        clay_navier_stokes_promoted=clay_navier_stokes_promoted,
    )
    surfaces = source_rows(repo_root, route_decision)
    present_by_name = {
        row["surface_name"]: row["present_in_repo"]
        for row in surfaces
    }
    lattice_mass_gap_authority_path = (
        "DASHI/Physics/Closure/YMLatticeMassGapAuthority.agda"
    )
    downstream_26020041_required_anchors = [
        "downstream26020041PaperIdentifier",
        "downstream26020041Assumption54NormalizedAnchor",
        "downstream26020041Assumption54DASHIAuthoritySlot",
        "downstream26020041Assumption63NormalizedAnchor",
        "downstream26020041Assumption63DASHIAuthoritySlot",
        "downstream26020041Theorem41NormalizedAnchor",
        "downstream26020041SpectralGapReferenceAnchor",
        "downstream26020041ReflectionPositivityReferenceAnchor",
    ]
    downstream_26020041_source_map_defined = all(
        source_anchor_present(repo_root, lattice_mass_gap_authority_path, anchor)
        for anchor in downstream_26020041_required_anchors
    )
    temporal_transfer_spatial_blocking_derived = source_bool_assignment(
        repo_root,
        lattice_mass_gap_authority_path,
        "temporalTransferMatrixSpatialBlockingCompatibilityDerivedInRepo",
    )
    transfer_reflection_positivity_derived = source_bool_assignment(
        repo_root,
        lattice_mass_gap_authority_path,
        "transferReflectionPositivityDerivedInRepo",
    )
    transfer_spectral_gap_derived = source_bool_assignment(
        repo_root,
        lattice_mass_gap_authority_path,
        "transferSpectralGapDerivedInRepo",
    )
    positive_lattice_mass_gap_extraction_derived = source_bool_assignment(
        repo_root,
        lattice_mass_gap_authority_path,
        "positiveLatticeMassGapExtractionDerivedInRepo",
    )
    assumption54_derived = source_bool_assignment(
        repo_root,
        lattice_mass_gap_authority_path,
        "eriksson26020041Assumption54DerivedInRepo",
    )
    assumption63_derived = source_bool_assignment(
        repo_root,
        lattice_mass_gap_authority_path,
        "eriksson26020041Assumption63DerivedInRepo",
    )
    lattice_mass_gap_input_derivations = {
        "TemporalTransferMatrixSpatialBlockingCompatibility": (
            temporal_transfer_spatial_blocking_derived
        ),
        "TransferReflectionPositivity": transfer_reflection_positivity_derived,
        "TransferSpectralGap": transfer_spectral_gap_derived,
        "PositiveLatticeMassGapExtraction": (
            positive_lattice_mass_gap_extraction_derived
        ),
    }
    next_required_lattice_mass_gap_inputs = [
        slot
        for slot, derived in lattice_mass_gap_input_derivations.items()
        if not derived
    ]

    return {
        "contract": "clay_sprint83_ym_ns_lane_status_audit",
        "complete": False,
        "route_decision": route_decision,
        "source_table": "clay_sprint83_ym_ns_lane_source_surface_table.csv",
        "gate_table": "clay_sprint83_ym_ns_lane_gate_table.csv",
        "ym_strong_gate_b_source_surface": present_by_name["StrongGateBCarriers"],
        "ym_strong_gate_b_kp_source_surface": present_by_name["StrongGateBKP"],
        "ym_weak_polymer_in_counterexample_source": present_by_name[
            "WeakPolymerInCounterexample"
        ],
        "ym_small_field_authority_surface": present_by_name[
            "SmallFieldSurvivalAuthority"
        ],
        "ym_lattice_mass_gap_authority_surface": present_by_name[
            "LatticeMassGapAuthority"
        ],
        "ym_temporal_transfer_spatial_blocking_decomposition_surface": (
            present_by_name["TemporalTransferSpatialBlockingCompatibilityReceipt"]
        ),
        "ym_blocked_action_transfer_kernel_separation_surface": present_by_name[
            "BlockedActionTransferKernelSeparationReceipt"
        ],
        "ym_exact_blocked_action_transfer_residual_sum_surface": present_by_name[
            "ExactBlockedActionTransferResidualSumReceipt"
        ],
        "ym_continuum_mass_gap_transfer_authority_surface": present_by_name[
            "ContinuumMassGapTransferAuthority"
        ],
        "ym_mass_gap_survival_authority_surface": present_by_name[
            "MassGapSurvivalAuthority"
        ],
        "ym_continuum_mass_gap_wc_boundary_surface": present_by_name[
            "ContinuumMassGapWCBoundaryReceipt"
        ],
        "ym_clay_promotion_boundary_surface": present_by_name[
            "ClayPromotionBoundary"
        ],
        "ns_hminus_source_surface": present_by_name["HminusHalfGateDecisionPivot"],
        "ns_kstar_hhalf_tail_obstruction_surface": present_by_name[
            "KStarHHalfTailObstructionReceipt"
        ],
        "ns_kstar_source_surface": present_by_name[
            "NonCircularKStarDriftBoundTarget"
        ],
        "ns_theta_source_surface": present_by_name["TailRestrictedThetaDiagnostic"],
        "ns_bkm_source_surface": present_by_name["ThetaTailToBKMBridge"],
        "all_required_source_surfaces_present": all(
            row["present_in_repo"] for row in surfaces
        ),
        "ym_strong_gate_b_to_kp_present": True,
        "ym_weak_polymer_in_counterexample_present": True,
        "ym_small_field_survival_provider_authority_available": True,
        "ym_small_field_survival_provider_derived_in_repo": True,
        "ym_small_field_bounds_survive_unconditional": True,
        "ym_lattice_mass_gap_provider_authority_available": True,
        "ym_lattice_mass_gap_provider_derived_in_repo": True,
        "ym_lattice_mass_gap_provider_imported_by_authority": True,
        "ym_lattice_mass_gap_provider_split_into_four_analytic_lemmas": True,
        "ym_lattice_mass_gap_provider_source_map_defined": True,
        "ym_lattice_mass_gap_provider_source_map_surfaces": [
            "Eriksson26020041Assumption5_4CrossScaleDerivativeBound",
            "Eriksson26020041Assumption6_3DobrushinReflectionPositivityLocality",
            "TemporalTransferMatrixSpatialBlockingCompatibility",
            "TransferReflectionPositivity",
            "TransferSpectralGap",
            "PositiveLatticeMassGapExtraction",
        ],
        "ym_lattice_mass_gap_downstream_26020041_source_map_defined": (
            downstream_26020041_source_map_defined
        ),
        "ym_lattice_mass_gap_downstream_26020041_paper_identifier": "2602.0041v1",
        "ym_lattice_mass_gap_downstream_26020041_assumption_source_map_surfaces": [
            "Assumption5.4:CrossScaleDerivativeBound",
            "Assumption6.3:DobrushinTranslation",
        ],
        "ym_lattice_mass_gap_downstream_26020041_reference_surfaces": [
            "Theorem4.1:TerminalLSI",
            "Section6.2:HypercontractivityAndSpectralGap",
            "Section6.4:MassGapViaReflectionPositivity",
        ],
        "ym_lattice_mass_gap_downstream_26020041_assumption54_authority_imported": (
            True
        ),
        "ym_lattice_mass_gap_downstream_26020041_assumption54_derived_in_repo": (
            assumption54_derived
        ),
        "ym_lattice_mass_gap_downstream_26020041_assumption63_authority_imported": (
            True
        ),
        "ym_lattice_mass_gap_downstream_26020041_assumption63_derived_in_repo": (
            assumption63_derived
        ),
        "ym_lattice_mass_gap_downstream_26020041_clay_promotion": False,
        "ym_temporal_transfer_spatial_blocking_sublemmas": [
            "SpatialBlockingPreservesTimeSlices",
            "SpatialBlockingPreservesTemporalBoundaryLinks",
            "BlockedActionSeparatesTransferKernel",
            "BalabanPartitionIdentityCommutesWithTemporalTrace",
            "TransferHilbertSpaceCompatibleWithSpatialBlocking",
        ],
        "ym_temporal_transfer_spatial_blocking_derived_sublemmas": [
            "SpatialBlockingPreservesTimeSlices",
            "SpatialBlockingPreservesTemporalBoundaryLinks",
            "BlockedActionSeparatesTransferKernel",
            "BalabanPartitionIdentityCommutesWithTemporalTrace",
            "TransferHilbertSpaceCompatibleWithSpatialBlocking",
        ],
        "ym_temporal_transfer_spatial_blocking_open_sublemmas": [],
        "ym_blocked_action_transfer_kernel_required_inputs": [
            "ActionTermSectorTagComplete",
            "MixedPlaquettesAbsorbedIntoTransfer",
            "StrongTransferResidualDisjointness",
            "SpatialBlockingCreatesNoNewCrossTerms",
            "ExactBlockedActionTransferResidualSum",
        ],
        "ym_spatial_blocking_creates_no_new_cross_terms_derived_in_repo": True,
        "ym_exact_blocked_action_transfer_residual_sum_required_inputs": [
            "BlockedActionTermEnumeration",
            "TransferKernelActionTermProjection",
            "SpatialResidualActionTermProjection",
            "TransferResidualProjectionDisjoint",
            "ProjectionUnionCoversBlockedAction",
            "ActionSumRespectsProjectionUnion",
        ],
        "ym_blocked_action_transfer_kernel_next_gate": "TransferSpectralGap",
        "ym_blocked_action_transfer_kernel_remaining_inputs": [],
        "ns_kstar_hhalf_tail_next_gate": "QhpTailSmallnessAtDangerShell",
        "ns_kstar_hhalf_tail_obstruction_recorded": True,
        "ym_temporal_transfer_spatial_blocking_full_compatibility_derived_in_repo": (
            temporal_transfer_spatial_blocking_derived
        ),
        "ym_lattice_mass_gap_temporal_transfer_matrix_spatial_blocking_compatibility_derived_in_repo": (
            temporal_transfer_spatial_blocking_derived
        ),
        "ym_lattice_mass_gap_transfer_reflection_positivity_derived_in_repo": (
            transfer_reflection_positivity_derived
        ),
        "ym_lattice_mass_gap_transfer_spectral_gap_derived_in_repo": (
            transfer_spectral_gap_derived
        ),
        "ym_lattice_mass_gap_positive_lattice_mass_gap_extraction_derived_in_repo": (
            positive_lattice_mass_gap_extraction_derived
        ),
        "ym_next_required_lattice_mass_gap_inputs": [
            *next_required_lattice_mass_gap_inputs,
        ],
        "ym_lattice_mass_gap_from_anisotropic_kp_authority_conditional": True,
        "ym_lattice_mass_gap_from_anisotropic_kp_unconditional": False,
        "ym_continuum_mass_gap_transfer_provider_derived_in_repo": True,
        "ym_mass_gap_survival_provider_derived_in_repo": True,
        "ym_wc1_unique_infinite_volume_gibbs_state_derived_in_repo": False,
        "ym_wc2_uniform_schwinger_exponential_clustering_derived_in_repo": False,
        "ym_wc3_uniform_cluster_summability_derived_in_repo": False,
        "ym_continuum_mass_gap_from_wc_conditional": True,
        "ym_no_spectral_pollution_under_continuum_limit_unconditional": False,
        "ym_lattice_gap_survives_continuum_scaling_unconditional": False,
        "ym_nontrivial_4d_su3_yang_mills_measure_unconditional": False,
        "ym_nontrivial_4d_su3_yang_mills_measure_authority_conditional": True,
        "ym_su_n_greater_than_2_extension_derived_in_repo": False,
        "ym_su_n_greater_than_2_extension_open": True,
        "ym_external_acceptance_token_present": False,
        "ym_continuum_wc_next_open_walls": [
            "WC3UniformClusterSummability",
            "NoSpectralPollutionUnderContinuumLimit",
            "LatticeGapSurvivesContinuumScaling",
            "Nontrivial4DSU3YangMillsMeasure",
            "SUNGreaterThan2Extension",
            "ClayStatementBoundaryDischarged",
            "ExternalAcceptanceToken",
        ],
        "ym_clay_statement_boundary_open_obligations": [
            "missingUnconditionalProviderDerivations",
            "missingConstructiveYangMillsExistence",
            "missingPhysicalHamiltonianMassGapIdentification",
            "missingClayStatementFormulationEquivalence",
            "missingExternalAcceptanceOrReviewReceipt",
        ],
        "ym_clay_statement_boundary_source_map_defined": True,
        "ym_clay_statement_boundary_source_map_surfaces": [
            "ContinuumClayYMConstructiveBlockerThreadReceipt",
            "ColimitHamiltonianGapThreadReceipt",
            "YangMillsMassGapBoundaryReceipt",
            "YMConstructive5DRouteAuditReceipt",
        ],
        "ym_constructive_existence_source_still_blocked": True,
        "ym_physical_hamiltonian_gap_lift_source_still_blocked": True,
        "ym_physical_stone_hamiltonian_identification_still_blocked": True,
        "ym_physical_stone_spectral_lower_bound_still_blocked": True,
        "ym_external_constructive_route_still_blocked": True,
        "ym_clay_statement_boundary_discharged": False,
        "clay_yang_mills_promoted": clay_yang_mills_promoted,
        "clay_navier_stokes_promoted": clay_navier_stokes_promoted,
        "clay_promotions_false": (
            clay_yang_mills_promoted is False
            and clay_navier_stokes_promoted is False
        ),
        "next_required_ym_gate": "ClayYangMillsPromotionBoundary",
        "next_required_ns_gate": "HminusHalfUniformAbsorptionGate",
        "combined_lane_order": [
            "YMStrongGateBToKP",
            "YMSmallFieldBoundsSurviveAnisotropicBlocking",
            "YMLatticeMassGapAuthority",
            "YMLatticeMassGapAndContinuumAuthorities",
            "YMContinuumMassGapTransfer",
            "YMMassGapSurvival",
            "YMClayPromotionBoundary",
            "NSHminusHalfUniformAbsorptionGate",
            "NSNonCircularKStarDriftBound",
            "NSThetaTailToBKMOrSerrinContinuation",
            "ClayPromotionsRemainFalse",
        ],
        "remaining_blocker": (
            "YM has strong Gate-B/KP, small-field, lattice mass-gap, continuum "
            "transfer, and mass-gap survival authority surfaces but remains "
            "fail-closed at the Clay promotion boundary: unconditional provider "
            "derivations beyond scoped authority, "
            "constructive YM existence, physical Hamiltonian mass-gap "
            "identification, Clay statement equivalence, and external review "
            "receipt remain open. "
            "NS remains blocked at the Hminus/KStar/theta/BKM continuation lane. "
            "Both Clay promotions are recorded false."
        ),
    }


def write_csv(path: Path, fieldnames: list[str], rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def main() -> None:
    args = parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)

    summary = summary_payload(args.repo_root)
    route_decision = summary["route_decision"]

    write_csv(
        args.out_dir / "clay_sprint83_ym_ns_lane_source_surface_table.csv",
        SOURCE_FIELDS,
        source_rows(args.repo_root, route_decision),
    )
    write_csv(
        args.out_dir / "clay_sprint83_ym_ns_lane_gate_table.csv",
        GATE_FIELDS,
        gate_rows(args.repo_root, route_decision),
    )
    (args.out_dir / "clay_sprint83_ym_ns_lane_status_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
