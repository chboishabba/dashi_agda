#!/usr/bin/env python3
"""Diagnostic harness for the YM continuum uniform rho bound."""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class Case:
    p: int
    rho_sup_tree: float
    casimir_shift_budget: float
    continuum_sup_proxy: float
    finite: bool


def build_case(p: int, c_g: float) -> Case:
    rho_sup = (p + 1) / math.pi
    continuum_sup = rho_sup + c_g
    return Case(p=p, rho_sup_tree=rho_sup, casimir_shift_budget=c_g, continuum_sup_proxy=continuum_sup, finite=math.isfinite(continuum_sup))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output")
    parser.add_argument("--cg", type=float, default=0.35)
    args = parser.parse_args()

    cases = [build_case(p, args.cg) for p in (2, 3, 5, 7)]
    payload = {
        "contract": "YM continuum uniform rho bound smoke",
        "diagnostic_only": True,
        "promotion": {"rho_bound_proved": False, "ym_clay_promoted": False, "terminal_promoted": False},
        "summary": {
            "all_finite": all(c.finite for c in cases),
            "max_continuum_sup_proxy": max(c.continuum_sup_proxy for c in cases),
            "mckay_sup_formula": "(p+1)/pi",
        },
        "cases": [asdict(c) for c in cases],
    }
    if args.json_output:
        with open(args.json_output, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
            handle.write("\n")
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"all_finite={payload['summary']['all_finite']}")
        print(f"max_continuum_sup_proxy={payload['summary']['max_continuum_sup_proxy']:.6f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
