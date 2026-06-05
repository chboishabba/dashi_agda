#!/usr/bin/env python3
"""Sprint 84 NS HminusHalf one-Sobolev-gap / Qhp target audit."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any


ROUTE_OPEN = "NS_HMINUS_HALF_ONE_SOBOLEV_GAP_QHP_OPEN"
ROUTE_SURFACE_MISSING = "NS_HMINUS_HALF_ONE_SOBOLEV_GAP_SURFACE_MISSING"
ROUTE_PROMOTION_VIOLATION = "NS_HMINUS_HALF_ONE_SOBOLEV_GAP_PROMOTION_VIOLATION"

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
            "surface_name": "OneSobolevGapTarget",
            "path": (
                "DASHI/Physics/Closure/"
                "NSSprint84HminusHalfOneSobolevGapTargetReceipt.agda"
            ),
            "required_anchor": "oneSobolevStepGapClosedHereIsFalse",
            "status": "ONE_SOBOLEV_GAP_TARGET_RECORDED_OPEN",
            "proved_in_repo": False,
        },
        {
            "surface_id": "S2",
            "surface_name": "NegativeSobolevDangerShell",
            "path": "DASHI/Physics/Closure/NSNegativeSobolevDangerShellReceipt.agda",
            "required_anchor": "canonicalHminusHalfHighHighDefectTheorem",
            "status": "HMINUS_HALF_HIGH_HIGH_DEFECT_THEOREM_NAMED",
            "proved_in_repo": False,
        },
        {
            "surface_id": "S3",
            "surface_name": "CanonicalHminusLane",
            "path": (
                "DASHI/Physics/Closure/"
                "NSSprint83HminusHalfCanonicalLaneReceipt.agda"
            ),
            "required_anchor": "hminusHalfHighHighDefectProvedHereIsFalse",
            "status": "CANONICAL_NS_HMINUS_LANE_OPEN",
            "proved_in_repo": False,
        },
        {
            "surface_id": "S4",
            "surface_name": "QhpNSCommutationPackage",
            "path": (
                "DASHI/Physics/Closure/"
                "NSSprint84HminusHalfOneSobolevGapTargetReceipt.agda"
            ),
            "required_anchor": "canonicalQhpNSCommutationPackage",
            "status": "NS_LOCAL_QHP_COMMUTATION_PACKAGE_FORMAL_RECORDED",
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
            "FormalQhpMapForNSBridge",
            "FORMAL_WITNESS_IN_REPO",
            "formal spatial-only Q_hp map usable against NS danger-shell data",
            True,
            False,
        ),
        (
            "G2",
            "QhpDangerShellProjectionCommutation",
            "FORMAL_WITNESS_IN_REPO",
            "Q_hp commutes with P_{>K*} / danger-shell projection",
            True,
            False,
        ),
        (
            "G3",
            "QhpKStarCutoffCommutation",
            "FORMAL_WITNESS_IN_REPO",
            "Q_hp commutes with K*(t) cutoff selection",
            True,
            False,
        ),
        (
            "G4",
            "QhpTailFluxPairingCommutation",
            "FORMAL_WITNESS_IN_REPO",
            "Q_hp preserves the H^{-1/2} x H^{1/2} tail-flux pairing",
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
            (
                "||P_{>K*}(u.grad u)||_{H^-1/2} "
                "<= epsilon*nu*||P_{>K*}u||_{H^3/2}"
            ),
            False,
            False,
        ),
        (
            "G7",
            "ClayNavierStokesPromoted",
            "FALSE_NO_PROMOTION",
            "Hminus/KStar/theta/BKM chain plus no finite-time blowup",
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
        "contract": "ns_sprint84_hminus_half_one_sobolev_gap_audit",
        "complete": False,
        "route_decision": route_decision,
        "source_table": "ns_sprint84_one_sobolev_gap_source_surface_table.csv",
        "gate_table": "ns_sprint84_one_sobolev_gap_gate_table.csv",
        "one_sobolev_gap_target_surface": present_by_name["OneSobolevGapTarget"],
        "negative_sobolev_danger_shell_surface": present_by_name[
            "NegativeSobolevDangerShell"
        ],
        "canonical_hminus_lane_surface": present_by_name["CanonicalHminusLane"],
        "qhp_ns_commutation_package_surface": present_by_name[
            "QhpNSCommutationPackage"
        ],
        "all_required_source_surfaces_present": all_surfaces_present,
        "one_sobolev_step_gap_target_recorded": True,
        "one_sobolev_step_gap_closed_here": False,
        "littlewood_paley_high_high_estimate_recorded": True,
        "littlewood_paley_reaches_h_three_four_squared": True,
        "needed_h_three_half_tail_dissipation_recorded": True,
        "littlewood_paley_estimate": (
            "sum_{j,k~N} ||Delta_j u . grad Delta_k u||_{H^-1/2} "
            "<= C*N^{3/2}*||P_{>K*}u||_{L2}^2 "
            "= C*||P_{>K*}u||_{H^{3/4}}^2"
        ),
        "needed_tail_dissipation_estimate": (
            "||P_{>K*}(u.grad u)||_{H^-1/2} "
            "<= epsilon*nu*||P_{>K*}u||_{H^{3/2}}, with epsilon < 1"
        ),
        "formal_qhp_map_available_for_ns_bridge": True,
        "qhp_commutes_with_danger_shell_projection": True,
        "qhp_commutes_with_kstar_cutoff": True,
        "qhp_commutes_with_tail_flux_pairing": True,
        "qhp_commutation_formal_witness_recorded": True,
        "qhp_commutation_proved_here": False,
        "ns1_hminus_half_high_high_defect_theorem_proved_here": False,
        "ns2_non_circular_kstar_drift_is_downstream": True,
        "ns3_edge_influx_theta_preservation_is_downstream": True,
        "ns4_theta_tail_to_bkm_continuation_is_downstream": True,
        "epsilon_below_one_coefficient_proved_here": False,
        "clay_navier_stokes_promoted": clay_navier_stokes_promoted,
        "clay_promotion_recorded_false": clay_navier_stokes_promoted is False,
        "next_required_gate": "AnalyticAbsorptionFromQhpCommutation",
        "highest_alpha_ns_path": [
            "FormalQhpMapForNSBridge",
            "QhpDangerShellProjectionCommutation",
            "QhpKStarCutoffCommutation",
            "QhpTailFluxPairingCommutation",
            "EpsilonBelowOneCoefficient",
            "HminusHalfHighHighDefectTheorem",
            "NonCircularKStarDriftBound",
            "ThetaTailToBKMOrSerrinContinuation",
        ],
        "remaining_blocker": (
            "turn the formal NS-local Q_hp commutation package into an "
            "epsilon<1 analytic absorption estimate and H^-1/2 high-high "
            "defect theorem before KStar drift, theta preservation, or "
            "BKM/Serrin continuation can be attempted"
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
        args.out_dir / "ns_sprint84_one_sobolev_gap_source_surface_table.csv",
        SOURCE_FIELDS,
        source_rows(args.repo_root, route_decision),
    )
    write_csv(
        args.out_dir / "ns_sprint84_one_sobolev_gap_gate_table.csv",
        GATE_FIELDS,
        gate_rows(route_decision),
    )
    (args.out_dir / "ns_sprint84_one_sobolev_gap_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
