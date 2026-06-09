#!/usr/bin/env python3
"""NS A8 -> A9 closure pipeline diagnostic harness.

Pure-stdlib integration smoke for the modeled chain

    A8 scale monotonicity -> A9 local vanishing / regularity closure.

This harness:
* computes the modeled A8 contraction factor
      q = (theta^2 + C*M) / (1 + C*M)
* iterates the scale recursion
      D_{theta r} <= q D_r + C_nl D_r^(1+alpha)
* detects whether the iterates vanish below a local regularity threshold
* emits a compact summary of the modeled A8 -> A9 closure chain

Diagnostic only. No theorem promotion.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


DEFAULT_OUTPUT = Path("outputs/ns_a8_a9_closure_pipeline_harness.json")
EPS = 1.0e-15
VALUE_CAP = 1.0e12


@dataclass(frozen=True)
class ClosureCase:
    name: str
    theta: float
    commutator_c: float
    type_i_m: float
    q: float
    q_is_contracting: bool
    nonlinear_c: float
    alpha: float
    initial_d: float
    regularity_threshold: float
    steps_taken: int
    final_d: float
    min_d: float
    max_d: float
    monotone_nonincreasing: bool
    crossed_regularity_threshold: bool
    crossed_absolute_vanishing_threshold: bool
    local_enstrophy_vanishes_modeled: bool
    a9_local_harmonic_regularization_triggered: bool
    chain_a8_to_a9_holds: bool
    sample_path: list[dict[str, float]]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--theta", type=float, default=0.5)
    parser.add_argument("--commutator-c", type=float, default=1.0)
    parser.add_argument("--type-i-m", type=float, default=0.125)
    parser.add_argument("--nonlinear-c", type=float, default=0.2)
    parser.add_argument("--alpha", type=float, default=0.5)
    parser.add_argument("--steps", type=int, default=48)
    parser.add_argument("--vanishing-threshold", type=float, default=1.0e-9)
    parser.add_argument("--regularity-threshold", type=float, default=1.0e-4)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args()


def compute_q(theta: float, commutator_c: float, type_i_m: float) -> float:
    cm = commutator_c * type_i_m
    return (theta * theta + cm) / (1.0 + cm)


def next_scale_value(d_value: float, q: float, nonlinear_c: float, alpha: float) -> float:
    if d_value <= 0.0:
        return 0.0
    if d_value >= VALUE_CAP:
        return VALUE_CAP
    exponent = 1.0 + alpha
    try:
        nonlinear_term = nonlinear_c * (d_value ** exponent)
    except OverflowError:
        return VALUE_CAP
    next_value = q * d_value + nonlinear_term
    if not math.isfinite(next_value):
        return VALUE_CAP
    return min(next_value, VALUE_CAP)


def build_sample_path(values: list[float], theta: float) -> list[dict[str, float]]:
    stride = max(1, len(values) // 10)
    samples = []
    for index in range(0, len(values), stride):
        samples.append(
            {
                "k": float(index),
                "scale_factor": theta ** index,
                "D": values[index],
            }
        )
    if not samples or samples[-1]["k"] != float(len(values) - 1):
        samples.append(
            {
                "k": float(len(values) - 1),
                "scale_factor": theta ** (len(values) - 1),
                "D": values[-1],
            }
        )
    return samples


def simulate_case(
    *,
    name: str,
    theta: float,
    commutator_c: float,
    type_i_m: float,
    nonlinear_c: float,
    alpha: float,
    initial_d: float,
    regularity_threshold: float,
    vanishing_threshold: float,
    steps: int,
) -> ClosureCase:
    q = compute_q(theta, commutator_c, type_i_m)
    values = [initial_d]
    current = initial_d
    for _ in range(steps):
        current = next_scale_value(current, q, nonlinear_c, alpha)
        values.append(current)

    monotone_nonincreasing = all(
        values[index + 1] <= values[index] + 1.0e-12
        for index in range(len(values) - 1)
    )
    final_d = values[-1]
    min_d = min(values)
    max_d = max(values)
    crossed_regularity_threshold = any(v <= regularity_threshold for v in values)
    crossed_absolute_vanishing_threshold = any(v <= vanishing_threshold for v in values)
    local_enstrophy_vanishes_modeled = final_d <= regularity_threshold
    a9_local_harmonic_regularization_triggered = local_enstrophy_vanishes_modeled
    chain_a8_to_a9_holds = (
        q < 1.0
        and monotone_nonincreasing
        and crossed_regularity_threshold
        and a9_local_harmonic_regularization_triggered
    )

    return ClosureCase(
        name=name,
        theta=theta,
        commutator_c=commutator_c,
        type_i_m=type_i_m,
        q=q,
        q_is_contracting=q < 1.0,
        nonlinear_c=nonlinear_c,
        alpha=alpha,
        initial_d=initial_d,
        regularity_threshold=regularity_threshold,
        steps_taken=steps,
        final_d=final_d,
        min_d=min_d,
        max_d=max_d,
        monotone_nonincreasing=monotone_nonincreasing,
        crossed_regularity_threshold=crossed_regularity_threshold,
        crossed_absolute_vanishing_threshold=crossed_absolute_vanishing_threshold,
        local_enstrophy_vanishes_modeled=local_enstrophy_vanishes_modeled,
        a9_local_harmonic_regularization_triggered=a9_local_harmonic_regularization_triggered,
        chain_a8_to_a9_holds=chain_a8_to_a9_holds,
        sample_path=build_sample_path(values, theta),
    )


def run(args: argparse.Namespace) -> dict[str, Any]:
    steps = min(args.steps, 24) if args.quick else args.steps

    threshold_scale = max(1.0 - compute_q(args.theta, args.commutator_c, args.type_i_m), EPS)
    modeled_smallness_threshold = (threshold_scale / max(args.nonlinear_c, EPS)) ** (1.0 / args.alpha)

    good_far = 0.25 * modeled_smallness_threshold
    good_near = 0.85 * modeled_smallness_threshold
    bad_near = 1.05 * modeled_smallness_threshold
    bad_far = 1.50 * modeled_smallness_threshold

    cases = [
        simulate_case(
            name="good_far_below_smallness_threshold",
            theta=args.theta,
            commutator_c=args.commutator_c,
            type_i_m=args.type_i_m,
            nonlinear_c=args.nonlinear_c,
            alpha=args.alpha,
            initial_d=good_far,
            regularity_threshold=args.regularity_threshold,
            vanishing_threshold=args.vanishing_threshold,
            steps=steps,
        ),
        simulate_case(
            name="good_near_smallness_threshold",
            theta=args.theta,
            commutator_c=args.commutator_c,
            type_i_m=args.type_i_m,
            nonlinear_c=args.nonlinear_c,
            alpha=args.alpha,
            initial_d=good_near,
            regularity_threshold=args.regularity_threshold,
            vanishing_threshold=args.vanishing_threshold,
            steps=steps,
        ),
        simulate_case(
            name="bad_near_smallness_threshold",
            theta=args.theta,
            commutator_c=args.commutator_c,
            type_i_m=args.type_i_m,
            nonlinear_c=args.nonlinear_c,
            alpha=args.alpha,
            initial_d=bad_near,
            regularity_threshold=args.regularity_threshold,
            vanishing_threshold=args.vanishing_threshold,
            steps=steps,
        ),
        simulate_case(
            name="bad_far_above_smallness_threshold",
            theta=args.theta,
            commutator_c=args.commutator_c,
            type_i_m=args.type_i_m,
            nonlinear_c=args.nonlinear_c,
            alpha=args.alpha,
            initial_d=bad_far,
            regularity_threshold=args.regularity_threshold,
            vanishing_threshold=args.vanishing_threshold,
            steps=steps,
        ),
    ]

    q_value = compute_q(args.theta, args.commutator_c, args.type_i_m)
    summary = {
        "q": q_value,
        "q_formula": "(theta^2 + C*M) / (1 + C*M)",
        "modeled_smallness_threshold": modeled_smallness_threshold,
        "good_cases_contract_to_regularity": all(
            case.chain_a8_to_a9_holds for case in cases[:2]
        ),
        "bad_cases_fail_chain": all(
            (not case.chain_a8_to_a9_holds) or case.final_d > case.regularity_threshold
            for case in cases[2:]
        ),
        "a8_scale_monotonicity_visible": all(
            case.q_is_contracting and case.monotone_nonincreasing for case in cases[:2]
        ),
        "a9_local_regularization_visible": all(
            case.local_enstrophy_vanishes_modeled and case.a9_local_harmonic_regularization_triggered
            for case in cases[:2]
        ),
    }

    return {
        "harness": "ns_a8_a9_closure_pipeline_harness",
        "scope": "finite_scale_recursion_and_local_closure_diagnostic",
        "a8_model": {
            "theta": args.theta,
            "commutator_c": args.commutator_c,
            "type_i_m": args.type_i_m,
            "q": q_value,
            "q_formula": "(theta^2 + C*M) / (1 + C*M)",
            "q_is_contracting": q_value < 1.0,
        },
        "a9_model": {
            "regularity_threshold": args.regularity_threshold,
            "vanishing_threshold": args.vanishing_threshold,
            "closure_criterion": "modeled local enstrophy below regularity threshold triggers local harmonic regularity",
        },
        "pipeline_threshold": {
            "smallness_threshold": modeled_smallness_threshold,
            "formula": "((1-q)/C_nl)^(1/alpha)",
        },
        "cases": [asdict(case) for case in cases],
        "summary": summary,
        "promotion": {
            "a8_proved": False,
            "a9_proved": False,
            "clay_ns": False,
            "terminal": False,
        },
    }


def main() -> int:
    args = parse_args()
    payload = run(args)
    text = json.dumps(payload, sort_keys=True)
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(text + "\n", encoding="utf-8")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
