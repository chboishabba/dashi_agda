#!/usr/bin/env python3
"""NS A8 scale monotonicity diagnostic harness.

Pure-stdlib numeric exercise of the modeled recursion

    D_{theta r} <= q * D_r + C * D_r^(1 + alpha),

with

    q = (theta^2 + C*M) / (1 + C*M).

This harness checks:

* admissibility of q for configurable theta, M, C_const, alpha;
* the claimed special case theta = 1/2 and C*M <= 1/8 => q <= 1/3;
* recursive decay over scales for starts below a modeled small-data threshold.

Diagnostic only. All promotion flags remain false.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


EPS = 1.0e-15


def modeled_q(theta: float, m_value: float, c_const: float) -> float:
    cm = c_const * m_value
    return (theta * theta + cm) / (1.0 + cm)


def recursion_rhs(d_value: float, q_value: float, c_const: float, alpha: float) -> float:
    if d_value <= 0.0:
        return 0.0
    return q_value * d_value + c_const * (d_value ** (1.0 + alpha))


def threshold_from_recursion(q_value: float, c_const: float, alpha: float) -> float:
    if c_const <= 0.0:
        return math.inf
    gap = 1.0 - q_value
    if gap <= 0.0:
        return 0.0
    return (gap / c_const) ** (1.0 / alpha)


def simulate_case(
    *,
    name: str,
    d0: float,
    q_value: float,
    c_const: float,
    alpha: float,
    theta: float,
    steps: int,
    divergence_cap: float,
) -> dict[str, Any]:
    values = [d0]
    ratios = []
    current = d0
    diverged = False
    for _ in range(steps):
        next_value = recursion_rhs(current, q_value, c_const, alpha)
        if not math.isfinite(next_value) or next_value >= divergence_cap:
            next_value = divergence_cap
            diverged = True
        ratios.append(next_value / max(current, EPS))
        values.append(next_value)
        current = next_value
        if diverged:
            break

    monotone_nonincreasing = all(values[i + 1] <= values[i] + 1.0e-12 for i in range(len(values) - 1))
    strictly_contracting = all(ratio < 1.0 - 1.0e-12 for ratio in ratios if math.isfinite(ratio))
    tends_to_zero = values[-1] <= max(1.0e-12, 1.0e-6 * max(d0, 1.0))
    scale_radii = [theta ** k for k in range(min(steps + 1, 10))]

    return {
        "name": name,
        "initial_data": d0,
        "step_count": steps,
        "final_value": values[-1],
        "min_value": min(values),
        "max_value": max(values),
        "monotone_nonincreasing": monotone_nonincreasing,
        "strictly_contracting": strictly_contracting,
        "tends_to_zero": tends_to_zero,
        "max_ratio": max(ratios) if ratios else 0.0,
        "min_ratio": min(ratios) if ratios else 0.0,
        "diverged": diverged,
        "scale_radii_prefix": scale_radii,
        "value_prefix": values[: min(len(values), 10)],
    }


def run(args: argparse.Namespace) -> dict[str, Any]:
    q_value = modeled_q(args.theta, args.m_value, args.c_const)
    cm = args.c_const * args.m_value
    threshold = threshold_from_recursion(q_value, args.c_const, args.alpha)
    divergence_cap = max(1.0, 10.0 * max(threshold, 1.0))
    special_case_q = modeled_q(0.5, args.special_case_m, args.special_case_c)
    special_case_cm = args.special_case_c * args.special_case_m

    steps = min(args.steps, 80) if args.quick else args.steps

    starts = [
        ("good_far_below_threshold", 0.50 * threshold if math.isfinite(threshold) else 0.05),
        ("good_near_threshold", 0.95 * threshold if math.isfinite(threshold) else 0.095),
        ("bad_near_threshold", 1.05 * threshold if math.isfinite(threshold) else 0.105),
        ("bad_far_above_threshold", 1.50 * threshold if math.isfinite(threshold) else 0.15),
    ]

    cases = [
        simulate_case(
            name=name,
            d0=value,
            q_value=q_value,
            c_const=args.c_const,
            alpha=args.alpha,
            theta=args.theta,
            steps=steps,
            divergence_cap=divergence_cap,
        )
        for name, value in starts
    ]

    good_cases = cases[:2]
    bad_cases = cases[2:]

    payload = {
        "harness": "ns_a8_scale_monotonicity_harness",
        "scope": "finite_recursion_diagnostic_not_ns_clay_proof",
        "parameters": {
            "theta": args.theta,
            "M": args.m_value,
            "C_const": args.c_const,
            "alpha": args.alpha,
            "steps": steps,
            "quick": args.quick,
        },
        "recursion": {
            "equation": "D_next <= q * D + C * D^(1+alpha)",
            "q_formula": "(theta^2 + C*M) / (1 + C*M)",
            "q_value": q_value,
            "q_less_than_one": q_value < 1.0,
            "c_times_m": cm,
            "threshold": threshold,
            "threshold_formula": "((1-q)/C)^(1/alpha)",
            "divergence_cap": divergence_cap,
        },
        "special_case": {
            "theta": 0.5,
            "M": args.special_case_m,
            "C_const": args.special_case_c,
            "c_times_m": special_case_cm,
            "assumption_c_times_m_leq_one_eighth": special_case_cm <= 0.125 + 1.0e-15,
            "q_value": special_case_q,
            "q_leq_one_third": special_case_q <= (1.0 / 3.0) + 1.0e-15,
        },
        "cases": cases,
        "summary": {
            "good_cases_decay_to_zero": all(
                case["monotone_nonincreasing"] and case["strictly_contracting"] and case["tends_to_zero"]
                for case in good_cases
            ),
            "bad_cases_fail_to_decay": all(
                case["diverged"] or (not case["strictly_contracting"]) or (not case["tends_to_zero"])
                for case in bad_cases
            ),
            "iterates_to_zero_for_admissible_starts": all(case["tends_to_zero"] for case in good_cases),
            "special_case_claim_holds": special_case_cm <= 0.125 + 1.0e-15
            and special_case_q <= (1.0 / 3.0) + 1.0e-15,
        },
        "formal_model": {
            "O": "Single-file diagnostic harness for NS A8 recursion; no downstream proof authority.",
            "R": "Exercise the A8 scale-monotonicity recursion and the theta=1/2, C*M<=1/8 special case.",
            "C": "scripts/ns_a8_scale_monotonicity_harness.py",
            "S": "Finite recursion only; no PDE transport, no CKN proof, no Clay closure.",
            "L": "diagnostic harness -> local validation -> optional manifest integration; no theorem promotion.",
            "P": "Model q, threshold, and scale iteration directly with configurable parameters.",
            "G": "All promotion flags false; this artifact cannot certify A8, A9, NS Clay, or terminal authority.",
            "F": "Gap remains theorem-level PDE justification of the modeled recursion.",
        },
        "promotion": {
            "a8_proved": False,
            "clay_ns": False,
            "terminal": False,
        },
    }
    return payload


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--theta", type=float, default=0.5)
    parser.add_argument("--m-value", type=float, default=0.125)
    parser.add_argument("--c-const", type=float, default=1.0)
    parser.add_argument("--alpha", type=float, default=0.5)
    parser.add_argument("--steps", type=int, default=200)
    parser.add_argument("--special-case-m", type=float, default=0.125)
    parser.add_argument("--special-case-c", type=float, default=1.0)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output", type=Path, default=None)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload = run(args)
    text = json.dumps(payload, sort_keys=True)

    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(text + "\n", encoding="utf-8")

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        summary = payload["summary"]
        recursion = payload["recursion"]
        special_case = payload["special_case"]
        print("ns_a8_scale_monotonicity_harness")
        print(f"  q={recursion['q_value']:.12f} q<1={recursion['q_less_than_one']}")
        print(f"  threshold={recursion['threshold']:.12f}")
        print(
            "  special_case: C*M={:.12f} q={:.12f} q<=1/3={}".format(
                special_case["c_times_m"],
                special_case["q_value"],
                special_case["q_leq_one_third"],
            )
        )
        print(f"  good_cases_decay_to_zero={summary['good_cases_decay_to_zero']}")
        print(f"  bad_cases_fail_to_decay={summary['bad_cases_fail_to_decay']}")
        print("  promotion=false")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
