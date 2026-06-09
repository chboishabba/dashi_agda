#!/usr/bin/env python3
"""Sprint 92 master-WC3 row-sum calculation."""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import Any


Q_CURRENT = 0.23178189475262734
EXP_MINUS_4 = math.exp(-4)

ROW_FIELDS = [
    "group",
    "k",
    "adjoint_penalty",
    "row_sum",
    "m0",
    "passes_exp_minus_4",
    "margin_m0_minus_4",
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path("outputs/ym_sprint92_master_wc3"),
    )
    return parser.parse_args()


def row_sum(k: int, adjoint_penalty: float) -> float:
    # Convention used by the current sprint:
    # C_local = A / 2^(k+1), row = 18*C_local.
    return 18.0 * adjoint_penalty / (2 ** (k + 1))


def build_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for name, penalty in [("SU2", 1.0), ("SU3_conservative", 9 / 4)]:
        for k in range(8, 13):
            row = row_sum(k, penalty)
            m0 = -math.log(row)
            rows.append(
                {
                    "group": name,
                    "k": k,
                    "adjoint_penalty": penalty,
                    "row_sum": row,
                    "m0": m0,
                    "passes_exp_minus_4": row < EXP_MINUS_4,
                    "margin_m0_minus_4": m0 - 4,
                }
            )
    return rows


def first_safe_k(rows: list[dict[str, Any]], group: str) -> int:
    return min(
        row["k"]
        for row in rows
        if row["group"] == group and row["passes_exp_minus_4"]
    )


def summary_payload(rows: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "q": Q_CURRENT,
        "eta4_q": 4 * Q_CURRENT,
        "eta6_q": 6 * Q_CURRENT,
        "eta8_q": 8 * Q_CURRENT,
        "eta4_passes": 4 * Q_CURRENT < 1,
        "eta6_fails": 6 * Q_CURRENT > 1,
        "eta8_fails": 8 * Q_CURRENT > 1,
        "exp_minus_4": EXP_MINUS_4,
        "su2_first_safe_k": first_safe_k(rows, "SU2"),
        "su3_first_safe_k": first_safe_k(rows, "SU3_conservative"),
        "route_decision": "MASTER_WC3_SU3_CONSERVATIVE_CLOSES_ARITHMETICALLY_AT_K11",
        "continuum_wall": "CONTINUUM_LIMIT_MASS_GAP_NOT_KP_SPECTRAL_CONTINUITY",
        "clay_yang_mills_promoted": False,
        "remaining_open_lemmas": [
            "BalabanCMP98AveragingKernelIsProbability",
            "BalabanCMP116PolymerMassBound",
            "ContractionDeltaLowerBound",
            "UniformBoundForAllA",
            "WC3UniformInA",
            "UniformConnectedSchwingerDecay",
            "ContinuumLimitMassGap",
        ],
        "typed_proof_obligations": [
            {
                "sprint": "93",
                "record": "GaugeCovariantDobrushinComparison",
                "field": "contractionDeltaLowerBound",
                "type": "ContractionDeltaLowerBound",
                "derived_in_repo": False,
            },
            {
                "sprint": "94",
                "record": "UniformPolymerActivityFromDobrushin",
                "field": "uniformBoundForAllA",
                "type": "UniformBoundForAllA",
                "derived_in_repo": False,
            },
            {
                "sprint": "95",
                "record": "WC3UniformClusterSummability",
                "field": "uniformInA",
                "type": "WC3UniformInA",
                "derived_in_repo": False,
            },
            {
                "sprint": "95-96",
                "record": "NoSpectralPollutionUnderContinuumLimit",
                "field": "continuumLimitMassGap",
                "type": "ContinuumLimitMassGap",
                "derived_in_repo": False,
            },
        ],
    }


def write_outputs(rows: list[dict[str, Any]], summary: dict[str, Any], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "ym_sprint92_master_wc3_rows.json").write_text(
        json.dumps(rows, indent=2, sort_keys=True) + "\n"
    )
    (out_dir / "ym_sprint92_master_wc3_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n"
    )
    with (out_dir / "ym_sprint92_master_wc3_rows.csv").open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=ROW_FIELDS)
        writer.writeheader()
        writer.writerows(rows)


def main() -> int:
    args = parse_args()
    rows = build_rows()
    summary = summary_payload(rows)
    write_outputs(rows, summary, args.out_dir)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
