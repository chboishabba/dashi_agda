#!/usr/bin/env python3
"""Sprint 79 YM effective-action support graph audit.

The default data are intentionally fail-closed.  Known transfer-matrix
bookkeeping rows are recorded as absorbed, while the residual A1/support graph
is left unproved until the Agda theorem supplies spatial blocked-lattice
support for every residual effective-action polymer.
"""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any


Q_CURRENT = 0.23178189475262734
ETA_FINE_LATTICE_SPATIAL = 6
ETA_BLOCKED_L2 = 4
ETA_GENERIC_4D = 8

SUPPORT_FIELDS = [
    "polymer_id",
    "rg_scale_k",
    "source_term_class",
    "contains_temporal_link",
    "contains_mixed_temporal_spatial_plaquette",
    "absorbed_into_transfer_matrix",
    "residual_effective_action_term",
    "spatial_support_only",
    "blocked_lattice_polymer",
    "fine_lattice_eta",
    "blocked_lattice_eta",
    "kp_entropy_used",
    "route_decision",
]

ENTROPY_FIELDS = [
    "graph_id",
    "graph_convention",
    "eta",
    "q",
    "eta_q",
    "kp_closes",
    "route_decision",
]

DECISIONS = {
    "spatial_confirmed": "EFFECTIVE_ACTION_POLYMERS_SPATIAL_ONLY_CONFIRMED",
    "temporal_remains": "TEMPORAL_LINK_REMAINS_IN_RESIDUAL_EFFECTIVE_ACTION",
    "fine_eta6": "KP_GRAPH_IS_FINE_LATTICE_ETA6_BLOCKED",
    "blocked_eta4": "KP_GRAPH_IS_BLOCKED_L2_ETA4_CONFIRMED",
    "route_blocked": "ANISOTROPIC_KP_ROUTE_BLOCKED",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    return parser.parse_args()


def support_rows() -> list[dict[str, Any]]:
    return [
        {
            "polymer_id": "mixed_temporal_spatial_face_action",
            "rg_scale_k": "all",
            "source_term_class": "mixed_temporal_spatial_plaquette",
            "contains_temporal_link": True,
            "contains_mixed_temporal_spatial_plaquette": True,
            "absorbed_into_transfer_matrix": True,
            "residual_effective_action_term": False,
            "spatial_support_only": True,
            "blocked_lattice_polymer": True,
            "fine_lattice_eta": ETA_FINE_LATTICE_SPATIAL,
            "blocked_lattice_eta": ETA_BLOCKED_L2,
            "kp_entropy_used": ETA_BLOCKED_L2,
            "route_decision": DECISIONS["spatial_confirmed"],
        },
        {
            "polymer_id": "temporal_measure_factor_lambda_one",
            "rg_scale_k": "all",
            "source_term_class": "temporal_measure_factor",
            "contains_temporal_link": True,
            "contains_mixed_temporal_spatial_plaquette": False,
            "absorbed_into_transfer_matrix": True,
            "residual_effective_action_term": False,
            "spatial_support_only": True,
            "blocked_lattice_polymer": True,
            "fine_lattice_eta": ETA_FINE_LATTICE_SPATIAL,
            "blocked_lattice_eta": ETA_BLOCKED_L2,
            "kp_entropy_used": ETA_BLOCKED_L2,
            "route_decision": DECISIONS["spatial_confirmed"],
        },
        {
            "polymer_id": "large_field_cut_candidate_a1_open",
            "rg_scale_k": "0..8 or all under Nc authority",
            "source_term_class": "large_field_polymer",
            "contains_temporal_link": "UNPROVED_FALSE",
            "contains_mixed_temporal_spatial_plaquette": "UNPROVED_FALSE",
            "absorbed_into_transfer_matrix": False,
            "residual_effective_action_term": True,
            "spatial_support_only": False,
            "blocked_lattice_polymer": False,
            "fine_lattice_eta": ETA_FINE_LATTICE_SPATIAL,
            "blocked_lattice_eta": ETA_BLOCKED_L2,
            "kp_entropy_used": ETA_FINE_LATTICE_SPATIAL,
            "route_decision": DECISIONS["route_blocked"],
        },
        {
            "polymer_id": "residual_effective_action_graph_a1_open",
            "rg_scale_k": "all",
            "source_term_class": "residual_effective_action_term",
            "contains_temporal_link": "UNPROVED_FALSE",
            "contains_mixed_temporal_spatial_plaquette": "UNPROVED_FALSE",
            "absorbed_into_transfer_matrix": False,
            "residual_effective_action_term": True,
            "spatial_support_only": False,
            "blocked_lattice_polymer": False,
            "fine_lattice_eta": ETA_FINE_LATTICE_SPATIAL,
            "blocked_lattice_eta": ETA_BLOCKED_L2,
            "kp_entropy_used": ETA_FINE_LATTICE_SPATIAL,
            "route_decision": DECISIONS["fine_eta6"],
        },
    ]


def entropy_rows() -> list[dict[str, Any]]:
    return [
        {
            "graph_id": "generic_4d_baseline",
            "graph_convention": "fine_lattice_4d_2d",
            "eta": ETA_GENERIC_4D,
            "q": Q_CURRENT,
            "eta_q": ETA_GENERIC_4D * Q_CURRENT,
            "kp_closes": False,
            "route_decision": DECISIONS["route_blocked"],
        },
        {
            "graph_id": "fine_lattice_spatial_d3",
            "graph_convention": "fine_lattice_3d_2d_sp",
            "eta": ETA_FINE_LATTICE_SPATIAL,
            "q": Q_CURRENT,
            "eta_q": ETA_FINE_LATTICE_SPATIAL * Q_CURRENT,
            "kp_closes": False,
            "route_decision": DECISIONS["fine_eta6"],
        },
        {
            "graph_id": "blocked_l2_spatial_transfer",
            "graph_convention": "blocked_l2_faces_2d_sp_minus_2",
            "eta": ETA_BLOCKED_L2,
            "q": Q_CURRENT,
            "eta_q": ETA_BLOCKED_L2 * Q_CURRENT,
            "kp_closes": True,
            "route_decision": DECISIONS["blocked_eta4"],
        },
    ]


def residual_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [row for row in rows if row["residual_effective_action_term"] is True]


def summary_payload(rows: list[dict[str, Any]]) -> dict[str, Any]:
    residual = residual_rows(rows)
    pass_condition_met = all(
        row["spatial_support_only"] is True
        and row["blocked_lattice_polymer"] is True
        and row["kp_entropy_used"] == ETA_BLOCKED_L2
        for row in residual
    )
    temporal_support_unproved = any(
        row["contains_temporal_link"] != False  # noqa: E712 - explicit CSV value audit
        and row["absorbed_into_transfer_matrix"] is False
        for row in residual
    )
    fine_graph_remains = any(
        row["kp_entropy_used"] == ETA_FINE_LATTICE_SPATIAL for row in residual
    )
    return {
        "contract": "ym_sprint79_effective_action_support_audit",
        "support_table": "ym_sprint79_effective_action_support_table.csv",
        "kp_graph_entropy_table": "ym_sprint79_kp_graph_entropy_table.csv",
        "q_current": Q_CURRENT,
        "fine_lattice_eta": ETA_FINE_LATTICE_SPATIAL,
        "fine_lattice_eta_q": ETA_FINE_LATTICE_SPATIAL * Q_CURRENT,
        "fine_lattice_eta_blocks_kp": True,
        "blocked_lattice_eta": ETA_BLOCKED_L2,
        "blocked_lattice_eta_q": ETA_BLOCKED_L2 * Q_CURRENT,
        "blocked_l2_kp_arithmetic_closes": True,
        "generic_4d_eta": ETA_GENERIC_4D,
        "generic_4d_eta_q": ETA_GENERIC_4D * Q_CURRENT,
        "effective_action_polymers_spatial_only_for_a1": False,
        "polymer_defined_on_blocked_lattice": False,
        "kp_entropy_at_blocked_scale_l2": False,
        "temporal_entropy_quotient_halves_generic_4d_count": False,
        "pass_condition_met": pass_condition_met,
        "fail_condition_temporal_support_unproved_or_present": temporal_support_unproved,
        "fail_condition_kp_graph_fine_lattice_eta6": fine_graph_remains,
        "route_decision": (
            DECISIONS["blocked_eta4"] if pass_condition_met else DECISIONS["route_blocked"]
        ),
    }


def write_csv(path: Path, fields: list[str], rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def main() -> int:
    args = parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    rows = support_rows()
    write_csv(
        args.out_dir / "ym_sprint79_effective_action_support_table.csv",
        SUPPORT_FIELDS,
        rows,
    )
    write_csv(
        args.out_dir / "ym_sprint79_kp_graph_entropy_table.csv",
        ENTROPY_FIELDS,
        entropy_rows(),
    )
    (args.out_dir / "ym_sprint79_effective_action_spatial_a1_summary.json").write_text(
        json.dumps(summary_payload(rows), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
