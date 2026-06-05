#!/usr/bin/env python3
"""Sprint 81A YM anisotropic Assumption-A authority assembly audit."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any


L_BLOCK = 2
REFERENCE_K = 9
SPATIAL_LINK_MULTIPLICITY = 3
ISOTROPIC_LINK_MULTIPLICITY = 4
Q_CURRENT = 0.23178189475262734

ROUTE_DECISION = (
    "ANISOTROPIC_ASSUMPTION_A_AUTHORITY_ASSEMBLED_NO_CLAY_PROMOTION"
)

AUTHORITY_FIELDS = [
    "authority_id",
    "authority_name",
    "source",
    "statement",
    "accepted_as_authority",
    "proved_in_repo",
    "scope",
    "route_decision",
]

GATE_FIELDS = [
    "gate_id",
    "gate_name",
    "depends_on",
    "status",
    "proved_in_repo",
    "authority_dependent",
    "blocks_fixed_volume_uv_closure",
    "blocks_clay_promotion",
    "next_gate",
]

SCALE_FIELDS = [
    "k",
    "l_block",
    "spatial_link_count_factor",
    "per_link_oscillation_factor",
    "squared_sum_factor",
    "uniform_cq_factor",
    "ratio_to_isotropic_4c_squared",
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--max-k", type=int, default=12)
    return parser.parse_args()


def authority_rows() -> list[dict[str, Any]]:
    raw_rows = [
        (
            "A1",
            "BalabanCMP98AveragingLocality",
            "Balaban CMP 98, Averaging operations for lattice gauge theories",
            "locality/smoothing of Balaban averaging maps",
            True,
            False,
            "external_authority_for_Qhp_locality",
        ),
        (
            "A2",
            "BalabanCMP98LocalOscillationBoundForQhp",
            "Balaban CMP 98 specialized to half-plane/spatial Q_hp",
            "osc_e(Q_hp)<=C_local*L^(-2k)",
            True,
            False,
            "authority_input_not_internal_derivation",
        ),
        (
            "A3",
            "W1SpatialOnlyBlockingPreservesTemporalLinks",
            "YMSpatialOnlyBlockingTemporalLinks receipt",
            "spatial-only blocking preserves temporal links",
            True,
            True,
            "receipt_level_in_repo_support",
        ),
        (
            "A4",
            "SpatialOnlyLinkCount3L3k",
            "Sprint 80/81 arithmetic audit",
            "|Lambda^1_sp(k)|=3*L^(3k)",
            True,
            True,
            "in_repo_arithmetic",
        ),
    ]
    return [
        {
            "authority_id": authority_id,
            "authority_name": authority_name,
            "source": source,
            "statement": statement,
            "accepted_as_authority": accepted,
            "proved_in_repo": proved,
            "scope": scope,
            "route_decision": ROUTE_DECISION,
        }
        for authority_id, authority_name, source, statement, accepted, proved, scope
        in raw_rows
    ]


def gate_rows() -> list[dict[str, Any]]:
    raw_rows = [
        (
            "G1",
            "BalabanCMP98LocalOscillationBoundForQhp",
            "A1,A2",
            "ACCEPTED_AS_AUTHORITY_NOT_PROVED_IN_REPO",
            False,
            True,
            False,
            False,
            "LipschitzToSquaredOscillationForQhp",
        ),
        (
            "G2",
            "LipschitzToSquaredOscillationForQhp",
            "G1,A3,A4",
            "ARITHMETIC_DERIVED_CONDITIONAL_ON_AUTHORITY",
            True,
            True,
            False,
            False,
            "AnisotropicAssumptionA",
        ),
        (
            "G3",
            "AnisotropicAssumptionA",
            "G2",
            "ASSEMBLED_CONDITIONAL_ON_AUTHORITY",
            True,
            True,
            False,
            False,
            "FixedFiniteVolumeBlockedObservableContinuumLimit",
        ),
        (
            "G4",
            "FixedFiniteVolumeBlockedObservableContinuumLimit",
            "G3 + Eriksson26020077Theorem16Conditional",
            "UV_GATE_READY_CONDITIONAL",
            False,
            True,
            False,
            False,
            "EffectiveActionPolymersSpatialOnlyForA1",
        ),
        (
            "G5",
            "EffectiveActionPolymersSpatialOnlyForA1",
            "separate KP support lane",
            "OPEN_SEPARATE_KP_GATE",
            False,
            False,
            False,
            True,
            "PolymerDefinedOnBlockedLattice",
        ),
        (
            "G6",
            "ClayYangMillsPromoted",
            "mass gap + OS/Wightman + continuum transfer",
            "FALSE_NO_PROMOTION",
            False,
            False,
            False,
            True,
            "",
        ),
    ]
    return [
        {
            "gate_id": gate_id,
            "gate_name": gate_name,
            "depends_on": depends_on,
            "status": status,
            "proved_in_repo": proved,
            "authority_dependent": authority_dependent,
            "blocks_fixed_volume_uv_closure": blocks_uv,
            "blocks_clay_promotion": blocks_clay,
            "next_gate": next_gate,
        }
        for (
            gate_id,
            gate_name,
            depends_on,
            status,
            proved,
            authority_dependent,
            blocks_uv,
            blocks_clay,
            next_gate,
        ) in raw_rows
    ]


def scale_rows(max_k: int) -> list[dict[str, Any]]:
    return [
        {
            "k": k,
            "l_block": L_BLOCK,
            "spatial_link_count_factor": SPATIAL_LINK_MULTIPLICITY
            * (L_BLOCK ** (3 * k)),
            "per_link_oscillation_factor": L_BLOCK ** (-2 * k),
            "squared_sum_factor": SPATIAL_LINK_MULTIPLICITY
            * (L_BLOCK ** (-k)),
            "uniform_cq_factor": SPATIAL_LINK_MULTIPLICITY,
            "ratio_to_isotropic_4c_squared": (
                SPATIAL_LINK_MULTIPLICITY * (L_BLOCK ** (-k))
            )
            / ISOTROPIC_LINK_MULTIPLICITY,
        }
        for k in range(max_k + 1)
    ]


def summary_payload() -> dict[str, Any]:
    squared_sum_at_reference = SPATIAL_LINK_MULTIPLICITY * (
        L_BLOCK ** (-REFERENCE_K)
    )
    ratio_at_reference = squared_sum_at_reference / ISOTROPIC_LINK_MULTIPLICITY
    eta4 = 4 * Q_CURRENT
    eta6 = 6 * Q_CURRENT
    eta8 = 8 * Q_CURRENT
    return {
        "contract": "ym_sprint81a_anisotropic_assumption_a_authority_audit",
        "complete": False,
        "route_decision": ROUTE_DECISION,
        "authority_table": "ym_sprint81a_authority_table.csv",
        "gate_assembly_table": "ym_sprint81a_gate_assembly_table.csv",
        "scale_table": "ym_sprint81a_scale_table.csv",
        "balaban_cmp98_authority_accepted": True,
        "balaban_cmp98_local_oscillation_bound_for_qhp_proved_in_repo": False,
        "balaban_cmp98_local_oscillation_bound_for_qhp_authority_dependent": True,
        "lipschitz_to_squared_oscillation_for_qhp": True,
        "anisotropic_assumption_a_authority_conditional": True,
        "anisotropic_assumption_a_unconditional_in_repo": False,
        "fixed_finite_volume_blocked_uv_closure_authority_conditional": True,
        "fixed_finite_volume_blocked_uv_closure_promoted_unconditionally": False,
        "effective_action_polymers_spatial_only_for_a1": False,
        "polymer_defined_on_blocked_lattice": False,
        "kp_entropy_at_blocked_scale_l2": False,
        "all_diameter_weighted_kp": False,
        "mass_gap_promoted": False,
        "clay_yang_mills_promoted": False,
        "l_block": L_BLOCK,
        "reference_k": REFERENCE_K,
        "spatial_link_multiplicity": SPATIAL_LINK_MULTIPLICITY,
        "isotropic_link_multiplicity": ISOTROPIC_LINK_MULTIPLICITY,
        "uniform_constant_form": "C_Q=3*C_local^2",
        "qhp_per_link_bound_form": "osc_e(Q_hp)<=C_local*L^(-2k)",
        "squared_sum_form": (
            "3*L^(3k)*C_local^2*L^(-4k)=3*C_local^2*L^(-k)"
        ),
        "squared_sum_lipschitz_form": (
            "3*L^(3k)*C_local^2*C_F^2*L^(-4k)"
            "=3*C_local^2*C_F^2*L^(-k)"
        ),
        "squared_sum_factor_at_k9": squared_sum_at_reference,
        "ratio_at_k9_to_isotropic_4c_squared": ratio_at_reference,
        "percent_at_k9_relative_to_isotropic_4c_squared": (
            ratio_at_reference * 100.0
        ),
        "q_current": Q_CURRENT,
        "eta_threshold": 1 / Q_CURRENT,
        "eta4_q": eta4,
        "eta4_margin": 1.0 - eta4,
        "eta4_kp_arithmetic_closes": eta4 < 1.0,
        "eta6_q": eta6,
        "eta6_kp_arithmetic_fails": eta6 > 1.0,
        "eta8_q": eta8,
        "eta8_kp_arithmetic_fails": eta8 > 1.0,
        "next_required_gate": "EffectiveActionPolymersSpatialOnlyForA1",
        "next_required_gates": [
            "EffectiveActionPolymersSpatialOnlyForA1",
            "PolymerDefinedOnBlockedLattice",
            "KPEntropyAtBlockedScaleL2",
            "AllDiameterWeightedKP",
            "SmallFieldBoundsSurviveAnisotropicBlocking",
            "LatticeMassGapFromAnisotropicKP",
            "ThermodynamicLimit",
            "OSWightmanReconstruction",
            "ContinuumMassGapTransfer",
            "MassGapSurvival",
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
        args.out_dir / "ym_sprint81a_authority_table.csv",
        authority_rows(),
        AUTHORITY_FIELDS,
    )
    write_csv(
        args.out_dir / "ym_sprint81a_gate_assembly_table.csv",
        gate_rows(),
        GATE_FIELDS,
    )
    write_csv(
        args.out_dir / "ym_sprint81a_scale_table.csv",
        scale_rows(args.max_k),
        SCALE_FIELDS,
    )
    (args.out_dir / "ym_sprint81a_summary.json").write_text(
        json.dumps(summary_payload(), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
