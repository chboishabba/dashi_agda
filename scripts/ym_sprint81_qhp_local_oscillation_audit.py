#!/usr/bin/env python3
"""Sprint 81 YM Q_hp local-oscillation proof-attempt audit."""

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

ROUTE_DECISION = "BALABAN_CMP98_QHP_LOCAL_OSCILLATION_MISSING_FORMAL_LAYER"

MISSING_INPUT_FIELDS = [
    "input_id",
    "input_name",
    "needed_for",
    "in_repo_status",
    "available_in_repo",
    "replacement_or_source_needed",
]

ATTEMPT_FIELDS = [
    "attempt_id",
    "lemma_name",
    "depends_on",
    "candidate_statement",
    "in_repo_support",
    "proved_in_repo",
    "route_decision",
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


def missing_input_rows() -> list[dict[str, Any]]:
    raw_rows = [
        (
            "M1",
            "FormalOscillationSeminormForGaugeLinks",
            "defines osc_e on gauge-link dependent observables",
            "MISSING_FORMAL_DEFINITION",
            False,
            "formal oscillation seminorm over gauge links",
        ),
        (
            "M2",
            "FormalQhpBlockingMapDefinition",
            "defines Q_hp_{ell,k} as a half-plane/spatial Balaban averaging map",
            "MISSING_FORMAL_DEFINITION",
            False,
            "formal fine/coarse gauge configuration map",
        ),
        (
            "M3",
            "BalabanCMP98AveragingLocalityImported",
            "imports the CMP 98 averaging locality theorem as a typed lemma",
            "MISSING_IMPORTED_THEOREM",
            False,
            "primary-source CMP 98 locality lemma specialized to repo carriers",
        ),
        (
            "M4",
            "QhpPerLinkInfluenceConeLMinus2k",
            "specializes locality to osc_e(Q_hp)<=C_local*L^(-2k)",
            "MISSING_PROOF_OBJECT",
            False,
            "per-link influence cone bound for Q_hp",
        ),
    ]
    return [
        {
            "input_id": input_id,
            "input_name": input_name,
            "needed_for": needed_for,
            "in_repo_status": status,
            "available_in_repo": available,
            "replacement_or_source_needed": source,
        }
        for input_id, input_name, needed_for, status, available, source in raw_rows
    ]


def attempt_rows() -> list[dict[str, Any]]:
    raw_rows = [
        (
            "A1",
            "W1SpatialOnlyBlockingPreservesTemporalLinks",
            "YMSpatialOnlyBlockingTemporalLinks",
            "spatial-only blocking preserves temporal links",
            "RECEIPT_LEVEL_AVAILABLE",
            True,
        ),
        (
            "A2",
            "Sprint80ConditionalArithmeticShell",
            "ClaySprintEightyYMAnisotropicAssumptionAProofPlanReceipt",
            "3*L^(3k)*C_local^2*L^(-4k)=3*C_local^2*L^(-k)",
            "ARITHMETIC_AVAILABLE_CONDITIONAL",
            True,
        ),
        (
            "A3",
            "BalabanCMP98LocalOscillationBoundForQhp",
            "M1+M2+M3+M4",
            "osc_e(Q_hp)<=C_local*L^(-2k) for spatial links e",
            "BLOCKED_BY_MISSING_FORMAL_LAYER",
            False,
        ),
        (
            "A4",
            "LipschitzToSquaredOscillationForQhp",
            "BalabanCMP98LocalOscillationBoundForQhp + LipschitzFunction F",
            "sum_spatial_e osc_e(F o Q_hp)^2 <= 3*C_local^2*Lip(F)^2",
            "OPEN_AFTER_A3",
            False,
        ),
        (
            "A5",
            "AnisotropicAssumptionA",
            "A3+A4",
            "Eriksson 2602.0077 Assumption A for Q_hp",
            "OPEN_FAIL_CLOSED",
            False,
        ),
    ]
    return [
        {
            "attempt_id": attempt_id,
            "lemma_name": lemma_name,
            "depends_on": depends_on,
            "candidate_statement": candidate_statement,
            "in_repo_support": support,
            "proved_in_repo": proved,
            "route_decision": ROUTE_DECISION,
        }
        for (
            attempt_id,
            lemma_name,
            depends_on,
            candidate_statement,
            support,
            proved,
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
    return {
        "contract": "ym_sprint81_qhp_local_oscillation_audit",
        "complete": False,
        "clay_yang_mills_promoted": False,
        "route_decision": ROUTE_DECISION,
        "missing_input_table": (
            "ym_sprint81_qhp_local_oscillation_missing_inputs.csv"
        ),
        "attempt_table": "ym_sprint81_qhp_local_oscillation_attempts.csv",
        "scale_table": "ym_sprint81_qhp_local_oscillation_scale_table.csv",
        "l_block": L_BLOCK,
        "reference_k": REFERENCE_K,
        "spatial_link_multiplicity": SPATIAL_LINK_MULTIPLICITY,
        "isotropic_link_multiplicity": ISOTROPIC_LINK_MULTIPLICITY,
        "spatial_link_count_form": "3*L^(3k)",
        "qhp_per_link_bound_form": "osc_e(Q_hp)<=C_local*L^(-2k)",
        "squared_sum_form": (
            "3*L^(3k)*C_local^2*L^(-4k)=3*C_local^2*L^(-k)"
        ),
        "uniform_constant_form": "C_Q=3*C_local^2",
        "squared_sum_factor_at_k9": squared_sum_at_reference,
        "ratio_at_k9_to_isotropic_4c_squared": ratio_at_reference,
        "percent_at_k9_relative_to_isotropic_4c_squared": (
            ratio_at_reference * 100.0
        ),
        "w1_spatial_only_blocking_available": True,
        "sprint80_arithmetic_shell_available": True,
        "conditional_volume_arithmetic_closes": True,
        "formal_oscillation_seminorm_for_gauge_links": False,
        "formal_qhp_blocking_map_definition": False,
        "balaban_cmp98_averaging_locality_imported": False,
        "qhp_per_link_influence_cone_l_minus_2k": False,
        "balaban_cmp98_local_oscillation_bound_for_qhp": False,
        "lipschitz_to_squared_oscillation_for_qhp": False,
        "anisotropic_assumption_a": False,
        "fixed_finite_volume_blocked_uv_closure_promoted": False,
        "mass_gap_promoted": False,
        "missing_formal_inputs": [
            "FormalOscillationSeminormForGaugeLinks",
            "FormalQhpBlockingMapDefinition",
            "BalabanCMP98AveragingLocalityImported",
            "QhpPerLinkInfluenceConeLMinus2k",
        ],
        "next_required_lemma": "BalabanCMP98LocalOscillationBoundForQhp",
        "next_required_lemmas": [
            "FormalOscillationSeminormForGaugeLinks",
            "FormalQhpBlockingMapDefinition",
            "BalabanCMP98AveragingLocalityImported",
            "QhpPerLinkInfluenceConeLMinus2k",
            "BalabanCMP98LocalOscillationBoundForQhp",
            "LipschitzToSquaredOscillationForQhp",
            "AnisotropicAssumptionA",
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
        args.out_dir / "ym_sprint81_qhp_local_oscillation_missing_inputs.csv",
        missing_input_rows(),
        MISSING_INPUT_FIELDS,
    )
    write_csv(
        args.out_dir / "ym_sprint81_qhp_local_oscillation_attempts.csv",
        attempt_rows(),
        ATTEMPT_FIELDS,
    )
    write_csv(
        args.out_dir / "ym_sprint81_qhp_local_oscillation_scale_table.csv",
        scale_rows(args.max_k),
        SCALE_FIELDS,
    )
    (args.out_dir / "ym_sprint81_qhp_local_oscillation_summary.json").write_text(
        json.dumps(summary_payload(), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
