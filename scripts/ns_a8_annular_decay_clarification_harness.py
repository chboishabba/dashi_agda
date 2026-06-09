#!/usr/bin/env python3
"""Finite proxy harness for the NS A8 annular decay clarification."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class CaseResult:
    theta: float
    c_times_m: float
    higher_c: float
    alpha: float
    q: float
    final_defect: float
    q_lt_one: bool
    monotone_decay: bool


def q_value(theta: float, c_times_m: float) -> float:
    return (theta * theta + c_times_m) / (1.0 + c_times_m)


def iterate(theta: float, c_times_m: float, higher_c: float, alpha: float, initial: float, steps: int) -> CaseResult:
    q = q_value(theta, c_times_m)
    values = [initial]
    current = initial
    for _ in range(steps):
        current = q * current + higher_c * (current ** (1.0 + alpha))
        values.append(current)
    return CaseResult(
        theta=theta,
        c_times_m=c_times_m,
        higher_c=higher_c,
        alpha=alpha,
        q=q,
        final_defect=current,
        q_lt_one=q < 1.0,
        monotone_decay=all(values[i + 1] <= values[i] + 1.0e-12 for i in range(len(values) - 1)),
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output")
    args = parser.parse_args()

    cases = [
        iterate(0.5, 0.125, 0.04, 0.5, 0.02, 24),
        iterate(0.55, 0.10, 0.03, 0.5, 0.015, 24),
        iterate(0.6, 0.08, 0.03, 0.5, 0.01, 24),
    ]
    payload = {
        "contract": "NS A8 annular decay clarification proxy",
        "diagnostic_only": True,
        "promotion": {
            "a8_proved": False,
            "ns_clay_promoted": False,
            "terminal_promoted": False,
        },
        "summary": {
            "all_q_lt_one": all(case.q_lt_one for case in cases),
            "all_monotone_decay": all(case.monotone_decay for case in cases),
            "all_final_defects_small": all(case.final_defect < 1.0e-3 for case in cases),
        },
        "cases": [asdict(case) for case in cases],
    }

    if args.json_output:
        with open(args.json_output, "w", encoding="utf-8") as handle:
            json.dump(payload, handle, indent=2, sort_keys=True)
            handle.write("\n")

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"all_q_lt_one={payload['summary']['all_q_lt_one']}")
        print(f"all_monotone_decay={payload['summary']['all_monotone_decay']}")
        print(f"all_final_defects_small={payload['summary']['all_final_defects_small']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

