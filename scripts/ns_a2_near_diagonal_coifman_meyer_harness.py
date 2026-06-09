#!/usr/bin/env python3
"""Finite proxy harness for the NS A2 near-diagonal Coifman-Meyer route."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class RegimeResult:
    regime: str
    j: int
    k: int
    lhs_proxy: float
    tight_rhs_proxy: float
    naive_rhs_proxy: float
    tight_route_passes: bool
    naive_route_passes: bool


def evaluate(regime: str, j: int, k: int, lhs_factor: float, naive_penalty: float) -> RegimeResult:
    min_gain = 2 ** min(j, k)
    lhs = lhs_factor * min_gain
    tight_rhs = 1.1 * min_gain
    naive_rhs = naive_penalty * (2 ** max(j, k))
    return RegimeResult(
        regime=regime,
        j=j,
        k=k,
        lhs_proxy=lhs,
        tight_rhs_proxy=tight_rhs,
        naive_rhs_proxy=naive_rhs,
        tight_route_passes=lhs <= tight_rhs + 1.0e-12,
        naive_route_passes=lhs <= naive_rhs + 1.0e-12,
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output")
    args = parser.parse_args()

    regimes = [
        evaluate("near_diagonal", 3, 4, 0.95, 0.30),
        evaluate("near_diagonal", 5, 5, 1.00, 0.28),
        evaluate("off_diagonal_loss", 2, 7, 1.08, 0.09),
    ]
    payload = {
        "contract": "NS A2 near-diagonal Coifman-Meyer proxy",
        "diagnostic_only": True,
        "promotion": {
            "a2_proved": False,
            "ns_clay_promoted": False,
            "terminal_promoted": False,
        },
        "summary": {
            "tight_route_passes_all": all(row.tight_route_passes for row in regimes),
            "naive_route_fails_some": any(not row.naive_route_passes for row in regimes),
        },
        "regimes": [asdict(row) for row in regimes],
    }

    if args.json_output:
        with open(args.json_output, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
            handle.write("\n")

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"tight_route_passes_all={payload['summary']['tight_route_passes_all']}")
        print(f"naive_route_fails_some={payload['summary']['naive_route_fails_some']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

