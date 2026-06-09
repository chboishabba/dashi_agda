#!/usr/bin/env python3
"""Sprint 80 YM anisotropic Assumption-A proof-plan audit."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path
from typing import Any


L_BLOCK = 2
SPATIAL_LINK_MULTIPLICITY = 3
ISOTROPIC_LINK_MULTIPLICITY = 4
REFERENCE_K = 9
SOURCE_FLOOR = 3.079
P0_AT_K8 = 3.057
P0_AT_K9 = 3.124
K_START_SPACETIME_FLOOR = 9
Q_CURRENT = 0.23178189475262734
ETA_BLOCKED_L2 = 4
ETA_FINE_LATTICE_SPATIAL = 6
ETA_GENERIC_4D = 8

STEP_FIELDS = [
    "step_id",
    "step_name",
    "input_claim",
    "expression",
    "status",
    "proved_in_repo",
    "blocks_anisotropic_assumption_a",
    "blocks_kp_gate_b1",
]

SCALE_FIELDS = [
    "k",
    "anisotropic_factor_relative_to_c_local_squared",
    "isotropic_factor_relative_to_c_local_squared",
    "ratio_to_isotropic_4c_squared",
    "uniform_bound_factor",
]

ROUTE_DECISION = "ANISOTROPIC_ASSUMPTION_A_PROOF_PLAN_READY_FAIL_CLOSED"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--max-k", type=int, default=12)
    return parser.parse_args()


def anisotropic_factor(k: int) -> float:
    return SPATIAL_LINK_MULTIPLICITY * (L_BLOCK ** (-k))


def isotropic_factor() -> float:
    return float(ISOTROPIC_LINK_MULTIPLICITY)


def scale_rows(max_k: int) -> list[dict[str, Any]]:
    return [
        {
            "k": k,
            "anisotropic_factor_relative_to_c_local_squared": anisotropic_factor(k),
            "isotropic_factor_relative_to_c_local_squared": isotropic_factor(),
            "ratio_to_isotropic_4c_squared": anisotropic_factor(k)
            / isotropic_factor(),
            "uniform_bound_factor": float(SPATIAL_LINK_MULTIPLICITY),
        }
        for k in range(max_k + 1)
    ]


def step_rows() -> list[dict[str, Any]]:
    raw_rows = [
        (
            "S1",
            "SpatialOnlyQhpLinkCount",
            "Q_hp averages spatial links only",
            "|Lambda^1_{k,sp}| = 3*L^(3k)",
            "RECORDED_INPUT",
            False,
            True,
            True,
        ),
        (
            "S2",
            "BalabanCMP98LocalOscillationBoundForQhp",
            "CMP 98 averaging locality must be specialized to Q_hp",
            "osc_e(Q_hp) <= C_local*L^(-2k)",
            "OPEN_THEOREM_OBJECT",
            False,
            True,
            True,
        ),
        (
            "S3",
            "SquaredOscillationProduct",
            "square the per-link bound and sum over spatial links",
            "3*L^(3k)*C_local^2*L^(-4k)=3*C_local^2*L^(-k)",
            "ARITHMETIC_CONDITIONAL",
            False,
            True,
            False,
        ),
        (
            "S4",
            "UniformAssumptionAConstant",
            "L>=2 and k>=0",
            "3*C_local^2*L^(-k) <= 3*C_local^2",
            "ARITHMETIC_CONDITIONAL",
            False,
            True,
            False,
        ),
        (
            "S5",
            "AnisotropicAssumptionA",
            "S1+S2+S3+S4 plus Lipschitz test observable control",
            "sum_spatial_e osc_e(F o Q_hp)^2 <= 3*C_local^2*Lip(F)^2",
            "OPEN_FAIL_CLOSED",
            False,
            True,
            False,
        ),
        (
            "S6",
            "EffectiveActionPolymersSpatialOnlyForA1",
            "shared anisotropic input layer also feeds KP support",
            "residual effective-action polymers have spatial blocked support",
            "OPEN_SEPARATE_GATE",
            False,
            False,
            True,
        ),
    ]
    return [
        {
            "step_id": step_id,
            "step_name": step_name,
            "input_claim": input_claim,
            "expression": expression,
            "status": status,
            "proved_in_repo": proved,
            "blocks_anisotropic_assumption_a": blocks_gate_a,
            "blocks_kp_gate_b1": blocks_gate_b1,
        }
        for (
            step_id,
            step_name,
            input_claim,
            expression,
            status,
            proved,
            blocks_gate_a,
            blocks_gate_b1,
        ) in raw_rows
    ]


def summary_payload() -> dict[str, Any]:
    reference_aniso = anisotropic_factor(REFERENCE_K)
    reference_iso = isotropic_factor()
    eta4_ratio = ETA_BLOCKED_L2 * Q_CURRENT
    eta6_ratio = ETA_FINE_LATTICE_SPATIAL * Q_CURRENT
    eta8_ratio = ETA_GENERIC_4D * Q_CURRENT
    return {
        "contract": "ym_sprint80_anisotropic_assumption_a_audit",
        "step_table": "ym_sprint80_anisotropic_assumption_a_steps.csv",
        "scale_table": "ym_sprint80_anisotropic_assumption_a_scale_table.csv",
        "route_decision": ROUTE_DECISION,
        "complete": False,
        "clay_yang_mills_promoted": False,
        "l_block": L_BLOCK,
        "reference_k": REFERENCE_K,
        "spatial_link_multiplicity": SPATIAL_LINK_MULTIPLICITY,
        "isotropic_link_multiplicity": ISOTROPIC_LINK_MULTIPLICITY,
        "spatial_link_count_form": "3*L^(3k)",
        "per_link_oscillation_decay_form": "C_local*L^(-2k)",
        "squared_oscillation_product_form": (
            "3*L^(3k)*C_local^2*L^(-4k)=3*C_local^2*L^(-k)"
        ),
        "spatial_only_oscillation_sum_l2_form": "3*C_local^2*2^(-k)",
        "uniform_cq_factor": SPATIAL_LINK_MULTIPLICITY,
        "uniform_constant_form": "C_Q=3*C_local^2",
        "source_floor": SOURCE_FLOOR,
        "p0_at_k8": P0_AT_K8,
        "p0_at_k9": P0_AT_K9,
        "p0_k8_below_source_floor": P0_AT_K8 < SOURCE_FLOOR,
        "p0_k9_above_source_floor": P0_AT_K9 > SOURCE_FLOOR,
        "p0_floor_track_explicit": True,
        "k_start_spacetime_floor": K_START_SPACETIME_FLOOR,
        "q_current": Q_CURRENT,
        "eta_blocked_l2": ETA_BLOCKED_L2,
        "eta_blocked_l2_q": eta4_ratio,
        "eta_blocked_l2_kp_arithmetic_closes": eta4_ratio < 1.0,
        "eta_fine_lattice_spatial": ETA_FINE_LATTICE_SPATIAL,
        "eta_fine_lattice_spatial_q": eta6_ratio,
        "eta_fine_lattice_spatial_kp_arithmetic_fails": eta6_ratio > 1.0,
        "eta_generic_4d": ETA_GENERIC_4D,
        "eta_generic_4d_q": eta8_ratio,
        "eta_generic_4d_kp_arithmetic_fails": eta8_ratio > 1.0,
        "anisotropic_factor_at_k9_relative_to_c_local_squared": reference_aniso,
        "isotropic_factor_relative_to_c_local_squared": reference_iso,
        "ratio_at_k9_to_isotropic_4c_squared": reference_aniso / reference_iso,
        "percent_at_k9_relative_to_c_local_squared": reference_aniso * 100.0,
        "percent_at_k9_relative_to_isotropic_4c_squared": (
            reference_aniso / reference_iso * 100.0
        ),
        "three_step_proof_plan_recorded": True,
        "conditional_volume_arithmetic_closes": True,
        "balaban_cmp98_local_oscillation_bound_for_qhp": False,
        "lipschitz_to_squared_oscillation_for_qhp": False,
        "anisotropic_assumption_a": False,
        "effective_action_polymers_spatial_only_for_a1": False,
        "fixed_finite_volume_blocked_uv_closure_promoted": False,
        "shared_input_layer_status": "RECORDED_BUT_NOT_ASSEMBLED",
        "next_required_lemmas": [
            "BalabanCMP98LocalOscillationBoundForQhp",
            "LipschitzToSquaredOscillationForQhp",
            "AnisotropicAssumptionA",
            "EffectiveActionPolymersSpatialOnlyForA1",
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
        args.out_dir / "ym_sprint80_anisotropic_assumption_a_steps.csv",
        step_rows(),
        STEP_FIELDS,
    )
    write_csv(
        args.out_dir / "ym_sprint80_anisotropic_assumption_a_scale_table.csv",
        scale_rows(args.max_k),
        SCALE_FIELDS,
    )
    (args.out_dir / "ym_sprint80_anisotropic_assumption_a_summary.json").write_text(
        json.dumps(summary_payload(), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
