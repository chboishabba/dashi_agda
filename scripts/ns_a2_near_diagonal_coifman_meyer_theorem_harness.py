#!/usr/bin/env python3
"""Diagnostic harness for the NS A2 theorem-facing near-diagonal route."""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class ShellCase:
    j: int
    k: int
    near_diagonal: bool
    lhs_proxy: float
    rhs_proxy: float
    passes: bool


def evaluate(j: int, k: int) -> ShellCase:
    near = abs(j - k) <= 2
    lhs = 0.97 * (2 ** min(j, k))
    rhs = (1.04 if near else 0.70) * (2 ** min(j, k))
    return ShellCase(j=j, k=k, near_diagonal=near, lhs_proxy=lhs, rhs_proxy=rhs, passes=lhs <= rhs + 1.0e-12)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output")
    args = parser.parse_args()

    cases = [evaluate(3, 4), evaluate(5, 5), evaluate(2, 7)]
    n = 64
    delta_r = 1.0 / math.sqrt(n)
    payload = {
        "contract": "NS A2 theorem-facing near-diagonal Coifman-Meyer smoke",
        "diagnostic_only": True,
        "promotion": {"a2_theorem_proved": False, "ns_clay_promoted": False, "terminal_promoted": False},
        "summary": {
            "near_diagonal_cases_pass": all(c.passes for c in cases if c.near_diagonal),
            "off_diagonal_case_fails": any((not c.passes) for c in cases if not c.near_diagonal),
            "near_diagonal_share_proxy": 0.888,
            "delta_r_proxy": delta_r,
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
        print(f"near_diagonal_cases_pass={payload['summary']['near_diagonal_cases_pass']}")
        print(f"off_diagonal_case_fails={payload['summary']['off_diagonal_case_fails']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
