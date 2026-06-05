#!/usr/bin/env python3
"""Sprint 81B YM effective-action spatial A1 support-interface audit."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any


Q_CURRENT = 0.23178189475262734
ROUTE_DECISION = "EFFECTIVE_ACTION_SUPPORT_INTERFACE_DEFINED_THEOREM_STILL_OPEN"

INTERFACE_FIELDS = [
    "interface_id",
    "interface_name",
    "needed_for",
    "status",
    "defined_in_repo",
    "blocks_effective_action_spatial_a1",
]

GATE_FIELDS = [
    "gate_id",
    "gate_name",
    "depends_on",
    "status",
    "proved_in_repo",
    "route_decision",
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    return parser.parse_args()


def interface_rows() -> list[dict[str, Any]]:
    raw_rows = [
        (
            "I1",
            "BalabanEffectiveAction",
            "carrier for S_k",
            "DEFINED_TYPED_CARRIER",
            True,
            False,
        ),
        (
            "I2",
            "Polymer",
            "carrier for gamma",
            "DEFINED_TYPED_CARRIER",
            True,
            False,
        ),
        (
            "I3",
            "PolymerIn",
            "membership relation PolymerIn S_k gamma",
            "DEFINED_TYPED_RELATION",
            True,
            False,
        ),
        (
            "I4",
            "LinkKindTemporalSpatial",
            "distinguish temporal and spatial support variables",
            "DEFINED_TYPED_CLASSIFICATION",
            True,
            False,
        ),
        (
            "I5",
            "TemporalLink",
            "typed predicate for temporal links",
            "DEFINED_TYPED_PREDICATE",
            True,
            False,
        ),
        (
            "I6",
            "SpatialLink",
            "typed predicate for spatial links",
            "DEFINED_TYPED_PREDICATE",
            True,
            False,
        ),
        (
            "I7",
            "PolymerSupport",
            "support set for residual polymer activities",
            "DEFINED_TYPED_PREDICATE",
            True,
            False,
        ),
        (
            "I8",
            "SpatialSupport",
            "predicate proving no temporal-link activity",
            "DEFINED_TYPED_PREDICATE",
            True,
            False,
        ),
        (
            "I9",
            "ResidualEffectiveActionTerm",
            "term class after transfer-matrix absorption",
            "DEFINED_TYPED_CARRIER",
            True,
            False,
        ),
        (
            "I10",
            "ActivityDependsOnlyOnLinksInsidePolymer",
            "Balaban/Eriksson A1-style activity locality",
            "DEFINED_TYPED_PREDICATE",
            True,
            False,
        ),
        (
            "I11",
            "TemporalMeasureFactorizationLambdaOneReconciled",
            "reconciles Sprint 71/73/78 lambda-one receipts",
            "DEFINED_RECONCILIATION_CARRIER",
            True,
            False,
        ),
        (
            "I12",
            "DefinedOnBlockedL2SpatialGraph",
            "prevents fallback to fine-lattice eta=6 graph",
            "DEFINED_TYPED_PREDICATE",
            True,
            False,
        ),
    ]
    return [
        {
            "interface_id": interface_id,
            "interface_name": interface_name,
            "needed_for": needed_for,
            "status": status,
            "defined_in_repo": defined,
            "blocks_effective_action_spatial_a1": blocks,
        }
        for interface_id, interface_name, needed_for, status, defined, blocks
        in raw_rows
    ]


def gate_rows() -> list[dict[str, Any]]:
    raw_rows = [
        (
            "G1",
            "EffectiveActionPolymersSpatialOnlyForA1",
            "I1-I11 + transfer absorption inputs",
            "OPEN_TYPED_INTERFACE_AVAILABLE",
            False,
        ),
        (
            "G2",
            "PolymerDefinedOnBlockedLattice",
            "G1 + I7",
            "OPEN_AFTER_G1",
            False,
        ),
        (
            "G3",
            "KPEntropyAtBlockedScaleL2",
            "G2 + L=2 face-count convention",
            "OPEN_AFTER_G2",
            False,
        ),
        (
            "G4",
            "AllDiameterWeightedKP",
            "G3 + 4q<1",
            "ARITHMETIC_READY_BUT_STRUCTURALLY_BLOCKED",
            False,
        ),
        (
            "G5",
            "LatticeMassGapFromAnisotropicKP",
            "G4 + small-field survival + transfer positivity",
            "OPEN_DOWNSTREAM",
            False,
        ),
        (
            "G6",
            "ClayYangMillsPromoted",
            "mass gap + continuum + OS/Wightman",
            "FALSE_NO_PROMOTION",
            False,
        ),
    ]
    return [
        {
            "gate_id": gate_id,
            "gate_name": gate_name,
            "depends_on": depends_on,
            "status": status,
            "proved_in_repo": proved,
            "route_decision": ROUTE_DECISION,
        }
        for gate_id, gate_name, depends_on, status, proved in raw_rows
    ]


def summary_payload() -> dict[str, Any]:
    eta4 = 4 * Q_CURRENT
    eta6 = 6 * Q_CURRENT
    eta8 = 8 * Q_CURRENT
    return {
        "contract": "ym_sprint81b_effective_action_support_interface_audit",
        "complete": False,
        "route_decision": ROUTE_DECISION,
        "interface_table": "ym_sprint81b_support_interface_table.csv",
        "gate_table": "ym_sprint81b_support_gate_table.csv",
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
        "effective_action_polymers_spatial_only_for_a1": False,
        "polymer_defined_on_blocked_lattice": False,
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
        "next_required_support_interface": [
            "BalabanEffectiveAction",
            "Polymer",
            "PolymerIn",
            "LinkKindTemporalSpatial",
            "TemporalLink",
            "SpatialLink",
            "PolymerSupport",
            "SpatialSupport",
            "ResidualEffectiveActionTerm",
            "ActivityDependsOnlyOnLinksInsidePolymer",
            "TemporalMeasureFactorizationLambdaOneReconciled",
            "DefinedOnBlockedL2SpatialGraph",
        ],
        "support_interface_defined": True,
        "spatial_only_bridge_defined": True,
        "next_required_kp_gates": [
            "ResidualEffectiveActionSpatialSupportEvidence",
            "EffectiveActionPolymersSpatialOnlyForA1",
            "PolymerDefinedOnBlockedLattice",
            "KPEntropyAtBlockedScaleL2",
            "AllDiameterWeightedKP",
        ],
    }


def write_csv(path: Path, rows: list[dict[str, Any]], fields: list[str]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def main() -> int:
    args = parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    write_csv(
        args.out_dir / "ym_sprint81b_support_interface_table.csv",
        interface_rows(),
        INTERFACE_FIELDS,
    )
    write_csv(
        args.out_dir / "ym_sprint81b_support_gate_table.csv",
        gate_rows(),
        GATE_FIELDS,
    )
    (args.out_dir / "ym_sprint81b_summary.json").write_text(
        json.dumps(summary_payload(), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
