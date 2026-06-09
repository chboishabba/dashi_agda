#!/usr/bin/env python3
"""A4 residual-positive error-budget threshold diagnostic.

This finite harness models the A4 Part IV bookkeeping:

  lower = c_A4 * eta
  errors = E_antipodal + E_low_vorticity + E_null_output + E_Bony

with the declared rates N^-1/2, N^-1/2, N^-1/2, and N^-1.  It is a numerical
receipt/falsification surface only, not an analytic proof.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class BudgetRow:
    eta: float
    c_a4: float
    big_c: float
    n: int
    epsilon: float
    delta: float
    antipodal_error: float
    low_vorticity_error: float
    null_output_error: float
    bony_error: float
    total_error: float
    lower_bound: float
    residual_margin: float
    r0: float
    residual_positive: bool


def row(eta: float, c_a4: float, big_c: float, n: int) -> BudgetRow:
    root = n ** -0.5
    epsilon = n ** -0.25
    delta = n ** -0.25
    antipodal = big_c * root
    low = big_c * root
    null = big_c * root
    bony = big_c / n
    total = antipodal + low + null + bony
    lower = c_a4 * eta
    margin = lower - total
    r0 = math.exp(-((2.0 * big_c) / max(c_a4 * eta, 1.0e-300)) ** 2)
    return BudgetRow(
        eta=eta,
        c_a4=c_a4,
        big_c=big_c,
        n=n,
        epsilon=epsilon,
        delta=delta,
        antipodal_error=antipodal,
        low_vorticity_error=low,
        null_output_error=null,
        bony_error=bony,
        total_error=total,
        lower_bound=lower,
        residual_margin=margin,
        r0=r0,
        residual_positive=margin > 0.0,
    )


def run(args: argparse.Namespace) -> dict[str, Any]:
    etas = [0.02, 0.05, 0.1] if args.quick else [0.01, 0.02, 0.05, 0.1]
    cvals = [0.05, 0.1, 0.25] if args.quick else [0.025, 0.05, 0.1, 0.25]
    nvals = [10_000, 100_000, 1_000_000] if args.quick else [10_000, 100_000, 1_000_000, 10_000_000]
    rows = [row(eta, c, args.big_c, n) for eta in etas for c in cvals for n in nvals]
    passing = [r for r in rows if r.residual_positive]
    first_pass_by_pair: dict[str, int | None] = {}
    for eta in etas:
        for c in cvals:
            key = f"eta={eta:.6g},c_A4={c:.6g}"
            candidates = [r.n for r in rows if r.eta == eta and r.c_a4 == c and r.residual_positive]
            first_pass_by_pair[key] = min(candidates) if candidates else None
    return {
        "harness": "ns_a4_error_budget_threshold_harness",
        "scope": "finite_error_budget_diagnostic_not_pde_proof",
        "rate_model": {
            "epsilon": "N^-1/4",
            "delta": "N^-1/4",
            "antipodal_low_null": "C*N^-1/2",
            "bony": "C*N^-1",
            "r0": "exp(-(2C/(c_A4*eta))^2)",
        },
        "rows": [asdict(r) for r in rows],
        "summary": {
            "row_count": len(rows),
            "passing_count": len(passing),
            "all_pairs_eventually_pass_in_grid": all(v is not None for v in first_pass_by_pair.values()),
            "first_pass_by_pair": first_pass_by_pair,
            "best_margin": max((r.residual_margin for r in rows), default=None),
            "worst_margin": min((r.residual_margin for r in rows), default=None),
        },
        "promotion": {
            "a4_proved": False,
            "clay_ns": False,
            "terminal": False,
        },
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--big-c", type=float, default=1.0)
    parser.add_argument("--json-output", type=Path)
    parser.add_argument("--json", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload = run(args)
    text = json.dumps(payload, indent=None if payload else 2, sort_keys=True)
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(text + "\n", encoding="utf-8")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
