#!/usr/bin/env python3
"""Diagnostic harness for the BT -> Euclidean universality gap transfer."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class GapTransferRow:
    p: int
    depth: int
    gamma_d: float
    beta: float
    perturbation: float
    euclidean_gap_lower_bound: float
    positive: bool


def build_rows(p: int, beta: float) -> list[GapTransferRow]:
    gammas = {2: 0.44, 3: 0.41, 4: 0.395, 5: 0.388}
    rows: list[GapTransferRow] = []
    for depth, gamma_d in gammas.items():
        perturbation = beta * (p ** (-depth))
        lower = gamma_d - perturbation
        rows.append(
            GapTransferRow(
                p=p,
                depth=depth,
                gamma_d=gamma_d,
                beta=beta,
                perturbation=perturbation,
                euclidean_gap_lower_bound=lower,
                positive=lower > 0.0,
            )
        )
    return rows


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output")
    parser.add_argument("--p", type=int, default=3)
    parser.add_argument("--beta", type=float, default=0.25)
    args = parser.parse_args()

    rows = build_rows(args.p, args.beta)
    payload = {
        "contract": "YM hyperbolic/Shimura to Euclidean universality smoke",
        "diagnostic_only": True,
        "promotion": {"universality_proved": False, "ym_clay_promoted": False, "terminal_promoted": False},
        "summary": {
            "all_gap_rows_positive": all(r.positive for r in rows),
            "min_euclidean_gap_lower_bound": min(r.euclidean_gap_lower_bound for r in rows),
            "formula": "gap(H_L^Eucl) >= gamma_d - C*beta*p^(-d)",
        },
        "rows": [asdict(r) for r in rows],
    }
    if args.json_output:
        with open(args.json_output, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
            handle.write("\n")
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"all_gap_rows_positive={payload['summary']['all_gap_rows_positive']}")
        print(f"min_euclidean_gap_lower_bound={payload['summary']['min_euclidean_gap_lower_bound']:.6f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
