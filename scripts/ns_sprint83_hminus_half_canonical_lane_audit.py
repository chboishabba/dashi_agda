#!/usr/bin/env python3
"""Sprint 83 NS HminusHalf canonical lane audit."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any


ROUTE_OPEN = "NS_HMINUS_HALF_CANONICAL_LANE_OPEN"
ROUTE_SURFACE_MISSING = "NS_HMINUS_HALF_CANONICAL_LANE_SURFACE_MISSING"
ROUTE_PROMOTION_VIOLATION = "NS_HMINUS_HALF_CANONICAL_LANE_PROMOTION_VIOLATION"

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
            "surface_name": "HminusHalfGateDecisionPivot",
            "path": "DASHI/Physics/Closure/NSHminusHalfGateDecisionPivotReceipt.agda",
            "required_anchor": "hMinusUniformAbsorptionProofActiveIsFalse",
            "status": "RECORDED_UNIFORM_ABSORPTION_OPEN",
            "proved_in_repo": False,
        },
        {
            "surface_id": "S2",
            "surface_name": "NonCircularKStarDriftBoundTarget",
            "path": "DASHI/Physics/Closure/NSNonCircularKStarDriftBoundTargetReceipt.agda",
            "required_anchor": "canonicalNonCircularKStarOpenObligations",
            "status": "TARGET_RECORDED_OPEN",
            "proved_in_repo": False,
        },
        {
            "surface_id": "S3",
            "surface_name": "TailRestrictedThetaDiagnostic",
            "path": "DASHI/Physics/Closure/NSTailRestrictedThetaDiagnosticReceipt.agda",
            "required_anchor": "claySeamUsesTailRestrictedTheta",
            "status": "DIAGNOSTIC_SURFACE_RECORDED_NO_PROMOTION",
            "proved_in_repo": False,
        },
        {
            "surface_id": "S4",
            "surface_name": "ThetaTailToBKMBridge",
            "path": "DASHI/Physics/Closure/NSThetaTailToBKMBridgeReceipt.agda",
            "required_anchor": "continuumBKMCriterionNotDischargedHere",
            "status": "CONDITIONAL_BRIDGE_RECORDED_OPEN",
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
    rows = []
    for row in required_surfaces():
        rows.append(
            {
                **row,
                "present_in_repo": surface_present(repo_root, row),
                "route_decision": route_decision,
            }
        )
    return rows


def gate_rows(route_decision: str) -> list[dict[str, Any]]:
    raw_rows = [
        (
            "G1",
            "HminusHalfUniformAbsorptionGate",
            "OPEN_NOT_PROVED_IN_REPO",
            "H^{-1/2} nonlinear-defect estimate at the danger shell",
            False,
            False,
        ),
        (
            "G2",
            "NonCircularKStarDriftBound",
            "OPEN_AFTER_HMINUS_HALF_GATE",
            "non-circular high-high control plus K*(t) drift containment",
            False,
            False,
        ),
        (
            "G3",
            "ThetaPreservationAtDangerShell",
            "OPEN_AFTER_KSTAR_DRIFT",
            "edge influx absorption and tail-restricted theta barrier",
            False,
            False,
        ),
        (
            "G4",
            "ThetaTailToBKMOrSerrinContinuation",
            "CONDITIONAL_BRIDGE_ONLY_OPEN_BOUNDARIES_REMAIN",
            "uniform K* bound, Sobolev tail control, and BKM/Serrin discharge",
            False,
            False,
        ),
        (
            "G5",
            "ClayNavierStokesPromoted",
            "FALSE_NO_PROMOTION",
            "all prior NS continuation and smoothness obligations",
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
        for (
            gate_id,
            gate_name,
            status,
            next_required_input,
            proved,
            clay_promotion,
        ) in raw_rows
    ]


def summary_payload(repo_root: Path) -> dict[str, Any]:
    surfaces = required_surfaces()
    present_by_name = {
        row["surface_name"]: surface_present(repo_root, row)
        for row in surfaces
    }
    all_surfaces_present = all(present_by_name.values())
    clay_navier_stokes_promoted = False
    route_decision = choose_route(
        all_surfaces_present=all_surfaces_present,
        clay_promoted=clay_navier_stokes_promoted,
    )

    return {
        "contract": "ns_sprint83_hminus_half_canonical_lane_audit",
        "complete": False,
        "route_decision": route_decision,
        "source_table": "ns_sprint83_hminus_half_source_surface_table.csv",
        "gate_table": "ns_sprint83_hminus_half_gate_table.csv",
        "hminus_half_source_surface": present_by_name[
            "HminusHalfGateDecisionPivot"
        ],
        "kstar_source_surface": present_by_name[
            "NonCircularKStarDriftBoundTarget"
        ],
        "theta_source_surface": present_by_name[
            "TailRestrictedThetaDiagnostic"
        ],
        "bkm_source_surface": present_by_name["ThetaTailToBKMBridge"],
        "all_required_source_surfaces_present": all_surfaces_present,
        "hminus_half_uniform_absorption_proved_in_repo": False,
        "non_circular_kstar_drift_bound_proved_in_repo": False,
        "theta_preservation_proved_in_repo": False,
        "bkm_or_serrin_continuation_discharged_in_repo": False,
        "clay_navier_stokes_promoted": clay_navier_stokes_promoted,
        "clay_promotion_recorded_false": clay_navier_stokes_promoted is False,
        "next_required_gate": "HminusHalfUniformAbsorptionGate",
        "canonical_lane_order": [
            "HminusHalfUniformAbsorptionGate",
            "NonCircularKStarDriftBound",
            "ThetaPreservationAtDangerShell",
            "ThetaTailToBKMOrSerrinContinuation",
            "ClayNavierStokesPromoted",
        ],
        "remaining_blocker": (
            "prove the non-circular H^{-1/2} nonlinear-defect estimate without "
            "importing H^{1/2}, Serrin, BKM, or stronger regularity"
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
        args.out_dir / "ns_sprint83_hminus_half_source_surface_table.csv",
        SOURCE_FIELDS,
        source_rows(args.repo_root, route_decision),
    )
    write_csv(
        args.out_dir / "ns_sprint83_hminus_half_gate_table.csv",
        GATE_FIELDS,
        gate_rows(route_decision),
    )
    (args.out_dir / "ns_sprint83_hminus_half_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n"
    )

    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
