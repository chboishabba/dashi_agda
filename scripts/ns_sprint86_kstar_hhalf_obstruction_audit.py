#!/usr/bin/env python3
"""Sprint 86 NS KStar/HHalf tail obstruction audit."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any


ROUTE_OPEN = "NS_SPRINT86_KSTAR_HHALF_OBSTRUCTION_OPEN"
ROUTE_SURFACE_MISSING = "NS_SPRINT86_KSTAR_HHALF_OBSTRUCTION_SURFACE_MISSING"
ROUTE_PROMOTION_VIOLATION = "NS_SPRINT86_KSTAR_HHALF_OBSTRUCTION_PROMOTION_VIOLATION"

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
            "surface_name": "Sprint86KStarHHalfTailObstruction",
            "path": "DASHI/Physics/Closure/NSSprint86KStarHHalfTailObstructionReceipt.agda",
            "required_anchor": "canonicalNSSprint86KStarHHalfTailObstructionReceipt",
            "status": "KSTAR_HHALF_TAIL_OBSTRUCTION_RECORDED_OPEN",
            "proved_in_repo": False,
        },
        {
            "surface_id": "S2",
            "surface_name": "Sprint84OneSobolevGapTarget",
            "path": (
                "DASHI/Physics/Closure/"
                "NSSprint84HminusHalfOneSobolevGapTargetReceipt.agda"
            ),
            "required_anchor": "canonicalQhpNSCommutationPackage",
            "status": "QHP_FORMAL_COMMUTATION_PACKAGE_RECORDED",
            "proved_in_repo": True,
        },
        {
            "surface_id": "S3",
            "surface_name": "NonCircularObstruction",
            "path": "DASHI/Physics/Closure/NSNonCircularObstructionReceipt.agda",
            "required_anchor": "canonicalNSNonCircularObstructionReceipt",
            "status": "HIGH_HIGH_PARAPRODUCT_CIRCULARITY_RECORDED",
            "proved_in_repo": False,
        },
        {
            "surface_id": "S4",
            "surface_name": "NegativeSobolevDangerShell",
            "path": "DASHI/Physics/Closure/NSNegativeSobolevDangerShellReceipt.agda",
            "required_anchor": "highHighDefectBoundProvedHere",
            "status": "HMINUS_HALF_HIGH_HIGH_DEFECT_TARGET_OPEN",
            "proved_in_repo": False,
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
            "QhpHighHighProductEstimate",
            "OPEN_NOT_PROVED_IN_REPO",
            "non-circular Q_hp high-high product estimate",
            False,
            False,
        ),
        (
            "G2",
            "QhpTailSmallnessAtDangerShell",
            "OPEN_NOT_PROVED_IN_REPO",
            "small H^{1/2} tail at danger shell",
            False,
            False,
        ),
        (
            "G3",
            "KStarAdmissibilityAloneControlsHHalfTail",
            "OPEN_NOT_PROVED_IN_REPO",
            "derive H^{1/2} tail control from KStar admissibility alone",
            False,
            False,
        ),
        (
            "G4",
            "KStarAdmissibilityAloneObstruction",
            "OBSTRUCTION_RECORDED",
            "avoid hidden H^1, H^{1/2}, Serrin, BKM, or stronger regularity",
            True,
            False,
        ),
        (
            "G5",
            "EpsilonBelowOneCoefficient",
            "OPEN_NOT_PROVED_IN_REPO",
            "epsilon < 1 high-high absorption coefficient",
            False,
            False,
        ),
        (
            "G6",
            "HminusHalfHighHighDefectTheorem",
            "OPEN_NOT_PROVED_IN_REPO",
            "H^{-1/2} high-high nonlinear-defect theorem",
            False,
            False,
        ),
        (
            "G7",
            "ClayNavierStokesPromoted",
            "FALSE_NO_PROMOTION",
            "Hminus/KStar/theta/BKM continuation chain",
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
    clay_navier_stokes_promoted = False
    route_decision = choose_route(
        all_surfaces_present=all_surfaces_present,
        clay_promoted=clay_navier_stokes_promoted,
    )

    return {
        "contract": "ns_sprint86_kstar_hhalf_obstruction_audit",
        "complete": False,
        "route_decision": route_decision,
        "source_table": "ns_sprint86_kstar_hhalf_obstruction_source_surface_table.csv",
        "gate_table": "ns_sprint86_kstar_hhalf_obstruction_gate_table.csv",
        "sprint86_kstar_hhalf_tail_obstruction_surface": present_by_name[
            "Sprint86KStarHHalfTailObstruction"
        ],
        "sprint84_one_sobolev_gap_target_surface": present_by_name[
            "Sprint84OneSobolevGapTarget"
        ],
        "non_circular_obstruction_surface": present_by_name[
            "NonCircularObstruction"
        ],
        "negative_sobolev_danger_shell_surface": present_by_name[
            "NegativeSobolevDangerShell"
        ],
        "all_required_source_surfaces_present": all_surfaces_present,
        "qhp_formal_commutation_package_recorded": True,
        "qhp_high_high_product_estimate_derived_in_repo": False,
        "qhp_tail_smallness_at_danger_shell_derived_in_repo": False,
        "kstar_admissibility_alone_controls_hhalf_tail_derived_in_repo": False,
        "kstar_admissibility_alone_obstruction_recorded": True,
        "h_one_half_tail_assumed_by_allowed_proof": False,
        "serrin_or_bkm_assumed_by_allowed_proof": False,
        "stronger_regularity_assumed_by_allowed_proof": False,
        "epsilon_below_one_coefficient_derived_in_repo": False,
        "hminus_half_high_high_defect_theorem_derived_in_repo": False,
        "clay_navier_stokes_promoted": clay_navier_stokes_promoted,
        "clay_promotion_recorded_false": clay_navier_stokes_promoted is False,
        "next_required_gate": "QhpTailSmallnessAtDangerShell",
        "open_obligations": [
            "QhpHighHighProductEstimate",
            "QhpTailSmallnessAtDangerShell",
            "KStarAdmissibilityAloneControlsHHalfTail",
            "EpsilonBelowOneCoefficient",
            "HminusHalfHighHighDefectTheorem",
        ],
        "remaining_blocker": (
            "derive small H^{1/2} tail control at the danger shell without "
            "importing hidden H^1, H^{1/2}, Serrin, BKM, or stronger regularity"
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
        args.out_dir / "ns_sprint86_kstar_hhalf_obstruction_source_surface_table.csv",
        SOURCE_FIELDS,
        source_rows(args.repo_root, route_decision),
    )
    write_csv(
        args.out_dir / "ns_sprint86_kstar_hhalf_obstruction_gate_table.csv",
        GATE_FIELDS,
        gate_rows(route_decision),
    )
    (args.out_dir / "ns_sprint86_kstar_hhalf_obstruction_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
