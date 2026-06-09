#!/usr/bin/env python3
"""Small diagnostic for the A8 scale-recursion surface.

This is a fail-closed local harness only. It models the recursion

    D_{theta r} <= q D_r + C D_r^(1+alpha)

with q(theta, M) = (theta^2 + C*M) / (1 + C*M),
checks q < 1 in admissible regimes, and iterates the recurrence.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass


@dataclass
class CaseResult:
    theta: float
    type_i_M: float
    structural_C: float
    higher_C: float
    alpha: float
    initial_D: float
    steps: int
    q: float
    q_lt_one: bool
    final_D: float
    monotone_nonincreasing: bool


def q_value(theta: float, type_i_M: float, structural_C: float) -> float:
    cm = structural_C * type_i_M
    return (theta * theta + cm) / (1.0 + cm)


def iterate_case(
    theta: float,
    type_i_M: float,
    structural_C: float,
    higher_C: float,
    alpha: float,
    initial_D: float,
    steps: int,
) -> CaseResult:
    q = q_value(theta, type_i_M, structural_C)
    values = [initial_D]
    current = initial_D
    for _ in range(steps):
        nxt = q * current + higher_C * (current ** (1.0 + alpha))
        values.append(nxt)
        current = nxt
    return CaseResult(
        theta=theta,
        type_i_M=type_i_M,
        structural_C=structural_C,
        higher_C=higher_C,
        alpha=alpha,
        initial_D=initial_D,
        steps=steps,
        q=q,
        q_lt_one=(q < 1.0),
        final_D=current,
        monotone_nonincreasing=all(
            values[i + 1] <= values[i] + 1.0e-12 for i in range(len(values) - 1)
        ),
    )


def build_cases(quick: bool) -> list[CaseResult]:
    if quick:
        specs = [
            (0.5, 0.125, 1.0, 0.05, 0.5, 0.02, 24),
            (0.5, 0.10, 1.0, 0.04, 0.5, 0.01, 24),
            (0.6, 0.08, 0.9, 0.03, 0.5, 0.015, 24),
        ]
    else:
        specs = [
            (0.5, 0.125, 1.0, 0.05, 0.5, 0.02, 80),
            (0.5, 0.10, 1.0, 0.04, 0.5, 0.01, 80),
            (0.6, 0.08, 0.9, 0.03, 0.5, 0.015, 80),
            (0.4, 0.12, 1.1, 0.02, 0.5, 0.02, 80),
        ]
    return [iterate_case(*spec) for spec in specs]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output")
    args = parser.parse_args()

    cases = build_cases(args.quick)
    q_bound_half_case = q_value(0.5, 0.125, 1.0)
    payload = {
        "contract": "A8 full local defect monotonicity diagnostic",
        "diagnostic_only": True,
        "promotion": {
            "a8_proved": False,
            "a9_proved": False,
            "ns_clay_promoted": False,
            "terminal_promoted": False,
        },
        "summary": {
            "all_q_lt_one": all(case.q_lt_one for case in cases),
            "all_monotone_nonincreasing": all(
                case.monotone_nonincreasing for case in cases
            ),
            "theta_half_cm_one_eighth_q": q_bound_half_case,
            "theta_half_cm_one_eighth_q_le_one_third": q_bound_half_case <= (1.0 / 3.0 + 1.0e-12),
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
        print(
            "theta_half_cm_one_eighth_q="
            f"{payload['summary']['theta_half_cm_one_eighth_q']:.6f}"
        )
        print(
            "theta_half_cm_one_eighth_q_le_one_third="
            f"{payload['summary']['theta_half_cm_one_eighth_q_le_one_third']}"
        )
        print(
            "all_monotone_nonincreasing="
            f"{payload['summary']['all_monotone_nonincreasing']}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
