#!/usr/bin/env python3
"""Sprint 86 YM blocked-action transfer-kernel separation audit."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any


ROUTE_OPEN = "YM_SPRINT86_BLOCKED_ACTION_TRANSFER_KERNEL_OPEN"
ROUTE_SURFACE_MISSING = "YM_SPRINT86_BLOCKED_ACTION_TRANSFER_KERNEL_SURFACE_MISSING"
ROUTE_PROMOTION_VIOLATION = "YM_SPRINT86_BLOCKED_ACTION_TRANSFER_KERNEL_PROMOTION_VIOLATION"

SOURCE_FIELDS = [
    "surface_id",
    "surface_name",
    "path",
    "required_anchor",
    "status",
    "present_in_repo",
    "proved_in_repo",
    "route_decision",
]

GATE_FIELDS = [
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
            "surface_id": "S1",
            "surface_name": "Sprint86BlockedActionTransferKernel",
            "path": (
                "DASHI/Physics/Closure/"
                "YMSprint86BlockedActionTransferKernelSeparationReceipt.agda"
            ),
            "required_anchor": (
                "canonicalYMSprint86BlockedActionTransferKernelSeparationReceipt"
            ),
            "status": "BLOCKED_ACTION_TRANSFER_KERNEL_DECOMPOSITION_RECORDED_OPEN",
            "proved_in_repo": False,
        },
        {
            "surface_id": "S2",
            "surface_name": "Sprint87ExactBlockedActionTransferResidualSum",
            "path": (
                "DASHI/Physics/Closure/"
                "YMSprint87ExactBlockedActionTransferResidualSumReceipt.agda"
            ),
            "required_anchor": (
                "canonicalYMSprint87ExactBlockedActionTransferResidualSumReceipt"
            ),
            "status": "EXACT_BLOCKED_ACTION_SUM_DECOMPOSITION_RECORDED_OPEN",
            "proved_in_repo": False,
        },
        {
            "surface_id": "S3",
            "surface_name": "Sprint85TemporalTransferSpatialBlocking",
            "path": (
                "DASHI/Physics/Closure/"
                "YMSprint85TemporalTransferSpatialBlockingCompatibilityReceipt.agda"
            ),
            "required_anchor": "blockedActionSeparatesTransferKernelDerivedInRepo",
            "status": "SPRINT85_TRANSFER_SPATIAL_BLOCKING_FULL_COMPATIBILITY_OPEN",
            "proved_in_repo": False,
        },
        {
            "surface_id": "S4",
            "surface_name": "StrongGateBCarriers",
            "path": "DASHI/Physics/Closure/YMStrongGateBCarriers.agda",
            "required_anchor": "strongActionTermTransferResidualDisjointnessFromSectors",
            "status": "STRONG_TRANSFER_RESIDUAL_DISJOINTNESS_DERIVED",
            "proved_in_repo": True,
        },
        {
            "surface_id": "S5",
            "surface_name": "TemporalTermsAbsorbedReceipt",
            "path": (
                "DASHI/Physics/Closure/"
                "ClaySprintSeventyEightYMTemporalTermsAbsorbedReceipt.agda"
            ),
            "required_anchor": "MixedPlaquettesAreTransferMatrixFaceAction",
            "status": "MIXED_PLAQUETTE_TRANSFER_SURFACE_AVAILABLE_CONDITIONAL",
            "proved_in_repo": True,
        },
        {
            "surface_id": "S6",
            "surface_name": "SpatialOnlyBlockingTemporalLinks",
            "path": "DASHI/Physics/Closure/YMSpatialOnlyBlockingTemporalLinks.agda",
            "required_anchor": "spatialOnlyBlockingPreservesTemporalLinks",
            "status": "SPATIAL_ONLY_TEMPORAL_LINK_PRESERVATION_PACKAGED",
            "proved_in_repo": True,
        },
    ]


def surface_present(repo_root: Path, row: dict[str, Any]) -> bool:
    path = repo_root / row["path"]
    if not path.exists():
        return False
    return row["required_anchor"] in path.read_text()


def choose_route(*, all_surfaces_present: bool, clay_promoted: bool) -> str:
    if clay_promoted:
        return ROUTE_PROMOTION_VIOLATION
    if not all_surfaces_present:
        return ROUTE_SURFACE_MISSING
    return ROUTE_OPEN


def source_rows(repo_root: Path, route_decision: str) -> list[dict[str, Any]]:
    return [
        {
            **row,
            "present_in_repo": surface_present(repo_root, row),
            "route_decision": route_decision,
        }
        for row in required_surfaces()
    ]


def gate_rows(route_decision: str) -> list[dict[str, Any]]:
    raw_rows = [
        (
            "G1",
            "ActionTermSectorTagComplete",
            "DERIVED_IN_REPO",
            "sector-tagged ActionTerm carrier",
            True,
            False,
        ),
        (
            "G2",
            "MixedPlaquettesAbsorbedIntoTransfer",
            "SURFACE_AVAILABLE_CONDITIONAL",
            "Sprint 71/78 mixed plaquette transfer face action",
            True,
            False,
        ),
        (
            "G3",
            "StrongTransferResidualDisjointness",
            "DERIVED_IN_REPO",
            "StrongActionTermTransferResidualDisjointness",
            True,
            False,
        ),
        (
            "G4",
            "SpatialBlockingCreatesNoNewCrossTerms",
            "DERIVED_IN_REPO",
            "no temporal leakage under spatial-only blocking",
            True,
            False,
        ),
        (
            "G5",
            "ExactBlockedActionTransferResidualSum",
            "OPEN_NOT_PROVED_IN_REPO",
            "S_k = spatial residual action + transfer kernel action",
            False,
            False,
        ),
        (
            "G6",
            "BlockedActionSeparatesTransferKernel",
            "OPEN_NOT_PROVED_IN_REPO",
            "assemble G1-G5 into Sprint 85 transfer-kernel separation",
            False,
            False,
        ),
        (
            "G7",
            "ClayYangMillsPromoted",
            "FALSE_NO_PROMOTION",
            "full transfer compatibility plus downstream lattice/continuum gates",
            False,
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
            "clay_promotion": clay_promotion,
            "route_decision": route_decision,
        }
        for gate_id, gate_name, status, next_required_input, proved, clay_promotion
        in raw_rows
    ]


def summary_payload(repo_root: Path) -> dict[str, Any]:
    present_by_name = {
        row["surface_name"]: surface_present(repo_root, row)
        for row in required_surfaces()
    }
    all_surfaces_present = all(present_by_name.values())
    clay_yang_mills_promoted = False
    route_decision = choose_route(
        all_surfaces_present=all_surfaces_present,
        clay_promoted=clay_yang_mills_promoted,
    )

    return {
        "contract": "ym_sprint86_blocked_action_transfer_kernel_audit",
        "complete": False,
        "route_decision": route_decision,
        "source_table": "ym_sprint86_blocked_action_transfer_kernel_source_surface_table.csv",
        "gate_table": "ym_sprint86_blocked_action_transfer_kernel_gate_table.csv",
        "sprint86_blocked_action_transfer_kernel_surface": present_by_name[
            "Sprint86BlockedActionTransferKernel"
        ],
        "sprint87_exact_blocked_action_transfer_residual_sum_surface": (
            present_by_name["Sprint87ExactBlockedActionTransferResidualSum"]
        ),
        "temporal_transfer_spatial_blocking_surface": present_by_name[
            "Sprint85TemporalTransferSpatialBlocking"
        ],
        "strong_gate_b_carrier_surface": present_by_name["StrongGateBCarriers"],
        "temporal_terms_absorbed_surface": present_by_name[
            "TemporalTermsAbsorbedReceipt"
        ],
        "spatial_only_blocking_temporal_links_surface": present_by_name[
            "SpatialOnlyBlockingTemporalLinks"
        ],
        "all_required_source_surfaces_present": all_surfaces_present,
        "action_term_sector_tag_complete_derived_in_repo": True,
        "mixed_plaquettes_absorbed_into_transfer_surface_available": True,
        "strong_transfer_residual_disjointness_derived_in_repo": True,
        "spatial_blocking_creates_no_new_cross_terms_derived_in_repo": True,
        "exact_blocked_action_transfer_residual_sum_derived_in_repo": False,
        "blocked_action_separates_transfer_kernel_derived_in_repo": False,
        "balaban_partition_identity_commutes_with_temporal_trace_derived_in_repo": False,
        "transfer_hilbert_space_compatible_with_spatial_blocking_derived_in_repo": False,
        "full_temporal_transfer_matrix_spatial_blocking_compatibility_derived_in_repo": False,
        "ym_temporal_transfer_spatial_blocking_open_sublemmas": [
            "BlockedActionSeparatesTransferKernel",
            "BalabanPartitionIdentityCommutesWithTemporalTrace",
            "TransferHilbertSpaceCompatibleWithSpatialBlocking",
        ],
        "blocked_action_transfer_kernel_required_inputs": [
            "ActionTermSectorTagComplete",
            "MixedPlaquettesAbsorbedIntoTransfer",
            "StrongTransferResidualDisjointness",
            "SpatialBlockingCreatesNoNewCrossTerms",
            "ExactBlockedActionTransferResidualSum",
        ],
        "exact_blocked_action_transfer_residual_sum_required_inputs": [
            "BlockedActionTermEnumeration",
            "TransferKernelActionTermProjection",
            "SpatialResidualActionTermProjection",
            "TransferResidualProjectionDisjoint",
            "ProjectionUnionCoversBlockedAction",
            "ActionSumRespectsProjectionUnion",
        ],
        "next_required_gate": "ExactBlockedActionTransferResidualSum",
        "clay_yang_mills_promoted": clay_yang_mills_promoted,
        "clay_promotion_recorded_false": clay_yang_mills_promoted is False,
        "remaining_blocker": (
            "prove blocked-action term enumeration, projection cover, and "
            "action-sum compatibility"
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

    summary = summary_payload(args.repo_root)
    route_decision = summary["route_decision"]

    write_csv(
        args.out_dir / "ym_sprint86_blocked_action_transfer_kernel_source_surface_table.csv",
        SOURCE_FIELDS,
        source_rows(args.repo_root, route_decision),
    )
    write_csv(
        args.out_dir / "ym_sprint86_blocked_action_transfer_kernel_gate_table.csv",
        GATE_FIELDS,
        gate_rows(route_decision),
    )
    (args.out_dir / "ym_sprint86_blocked_action_transfer_kernel_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
