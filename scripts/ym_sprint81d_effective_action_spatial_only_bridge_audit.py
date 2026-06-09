#!/usr/bin/env python3
"""Sprint 81D YM effective-action spatial-only bridge audit."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any


Q_CURRENT = 0.23178189475262734
ROUTE_DECISION = "EFFECTIVE_ACTION_SPATIAL_ONLY_BRIDGE_DEFINED_EVIDENCE_OPEN"

BRIDGE_FIELDS = [
    "bridge_id",
    "bridge_name",
    "input_required",
    "output_assembled",
    "status",
    "proved_in_repo",
]

GATE_FIELDS = [
    "gate_id",
    "gate_name",
    "status",
    "next_required_input",
    "route_decision",
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    return parser.parse_args()


def bridge_rows() -> list[dict[str, Any]]:
    raw_rows = [
        (
            "B1",
            "ResidualEffectiveActionSpatialSupportEvidence",
            "transfer absorption + lambda-one factorization + temporal support non-creation + spatial-only blocking",
            "spatial support for every PolymerIn S gamma",
            "OPEN_ANALYTIC_INPUT",
            False,
        ),
        (
            "B2",
            "effectiveActionPolymersSpatialOnlyForA1FromEvidence",
            "ResidualEffectiveActionSpatialSupportEvidence",
            "EffectiveActionPolymersSpatialOnlyForA1Theorem",
            "DEFINED_CONDITIONAL_ASSEMBLY",
            True,
        ),
        (
            "B3",
            "blockedL2SpatialGraphFromSpatialOnly",
            "EffectiveActionPolymersSpatialOnlyForA1Theorem + PolymerDefinedOnBlockedLatticeTheorem",
            "DefinedOnBlockedL2SpatialGraph gamma",
            "DEFINED_CONDITIONAL_ASSEMBLY",
            True,
        ),
    ]
    return [
        {
            "bridge_id": bridge_id,
            "bridge_name": bridge_name,
            "input_required": input_required,
            "output_assembled": output_assembled,
            "status": status,
            "proved_in_repo": proved,
        }
        for bridge_id, bridge_name, input_required, output_assembled, status, proved
        in raw_rows
    ]


def gate_rows() -> list[dict[str, Any]]:
    raw_rows = [
        (
            "G1",
            "EffectiveActionPolymersSpatialOnlyForA1",
            "CONDITIONAL_ASSEMBLY_DEFINED_EVIDENCE_OPEN",
            "ResidualEffectiveActionSpatialSupportEvidence",
        ),
        (
            "G2",
            "PolymerDefinedOnBlockedLattice",
            "OPEN_AFTER_SPATIAL_ONLY_THEOREM",
            "PolymerDefinedOnBlockedLatticeTheorem",
        ),
        (
            "G3",
            "KPEntropyAtBlockedScaleL2",
            "OPEN_AFTER_BLOCKED_LATTICE_THEOREM",
            "Blocked L=2 face-count theorem",
        ),
        (
            "G4",
            "AllDiameterWeightedKP",
            "ARITHMETIC_READY_BUT_STRUCTURALLY_BLOCKED",
            "KPEntropyAtBlockedScaleL2",
        ),
        (
            "G5",
            "ClayYangMillsPromoted",
            "FALSE_NO_PROMOTION",
            "mass gap + continuum + OS/Wightman",
        ),
    ]
    return [
        {
            "gate_id": gate_id,
            "gate_name": gate_name,
            "status": status,
            "next_required_input": next_required_input,
            "route_decision": ROUTE_DECISION,
        }
        for gate_id, gate_name, status, next_required_input in raw_rows
    ]


def summary_payload() -> dict[str, Any]:
    eta4 = 4 * Q_CURRENT
    eta6 = 6 * Q_CURRENT
    eta8 = 8 * Q_CURRENT
    return {
        "contract": "ym_sprint81d_effective_action_spatial_only_bridge_audit",
        "complete": False,
        "route_decision": ROUTE_DECISION,
        "bridge_table": "ym_sprint81d_spatial_only_bridge_table.csv",
        "gate_table": "ym_sprint81d_gate_table.csv",
        "support_interface_defined": True,
        "spatial_only_bridge_defined": True,
        "residual_effective_action_spatial_support_evidence": False,
        "effective_action_polymers_spatial_only_for_a1_conditional_assembly": True,
        "effective_action_polymers_spatial_only_for_a1_unconditional": False,
        "polymer_defined_on_blocked_lattice_unconditional": False,
        "kp_entropy_at_blocked_scale_l2": False,
        "all_diameter_weighted_kp": False,
        "mass_gap_promoted": False,
        "clay_yang_mills_promoted": False,
        "q_current": Q_CURRENT,
        "eta_threshold": 1 / Q_CURRENT,
        "eta4_q": eta4,
        "eta4_margin": 1.0 - eta4,
        "eta4_kp_arithmetic_closes": eta4 < 1.0,
        "eta6_q": eta6,
        "eta6_kp_arithmetic_fails": eta6 > 1.0,
        "eta8_q": eta8,
        "eta8_kp_arithmetic_fails": eta8 > 1.0,
        "next_required_gate": "ResidualEffectiveActionSpatialSupportEvidence",
        "next_exact_lemmas": [
            "ResidualEffectiveActionSpatialSupportEvidence",
            "EffectiveActionPolymersSpatialOnlyForA1",
            "PolymerDefinedOnBlockedLattice",
            "KPEntropyAtBlockedScaleL2",
            "AllDiameterWeightedKP",
        ],
        "remaining_blocker": (
            "prove the residual-support evidence from transfer absorption, "
            "lambda-one factorization, temporal support non-creation, and "
            "spatial-only blocking"
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

    bridges = bridge_rows()
    gates = gate_rows()
    summary = summary_payload()

    write_csv(
        args.out_dir / "ym_sprint81d_spatial_only_bridge_table.csv",
        BRIDGE_FIELDS,
        bridges,
    )
    write_csv(args.out_dir / "ym_sprint81d_gate_table.csv", GATE_FIELDS, gates)
    (args.out_dir / "ym_sprint81d_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n"
    )

    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
