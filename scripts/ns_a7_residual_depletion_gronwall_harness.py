#!/usr/bin/env python3
"""A7 residual depletion / Gronwall diagnostic harness.

Numerically integrates the scalar ODE

    D'(t) = -beta * D + C * D^(1 + alpha)

whose critical threshold is

    D_* = (beta / C)^(1 / alpha).

Below threshold, the right-hand side is negative and the trajectory should
deplete monotonically toward zero. Above threshold, the nonlinear source wins
and the trajectory should fail to deplete. This harness checks both regimes.

Diagnostic only. No theorem promotion.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


EPS = 1.0e-15


def rhs(d_value: float, beta: float, big_c: float, alpha: float) -> float:
    if d_value <= 0.0:
        return 0.0
    return -beta * d_value + big_c * (d_value ** (1.0 + alpha))


def rk4_step(d_value: float, dt: float, beta: float, big_c: float, alpha: float) -> float:
    k1 = rhs(d_value, beta, big_c, alpha)
    k2 = rhs(max(0.0, d_value + 0.5 * dt * k1), beta, big_c, alpha)
    k3 = rhs(max(0.0, d_value + 0.5 * dt * k2), beta, big_c, alpha)
    k4 = rhs(max(0.0, d_value + dt * k3), beta, big_c, alpha)
    next_value = d_value + (dt / 6.0) * (k1 + 2.0 * k2 + 2.0 * k3 + k4)
    return max(0.0, next_value)


def simulate_case(
    *,
    name: str,
    d0: float,
    beta: float,
    big_c: float,
    alpha: float,
    threshold: float,
    steps: int,
    dt: float,
    cap_multiplier: float,
) -> dict[str, Any]:
    values = [d0]
    times = [0.0]
    derivs = [rhs(d0, beta, big_c, alpha)]
    hit_cap = False

    cap = max(cap_multiplier * threshold, threshold + 1.0)
    current = d0
    for index in range(1, steps + 1):
        current = rk4_step(current, dt, beta, big_c, alpha)
        values.append(current)
        times.append(index * dt)
        derivs.append(rhs(current, beta, big_c, alpha))
        if current >= cap:
            hit_cap = True
            break

    monotone_decreasing = all(values[i + 1] <= values[i] + 1.0e-10 for i in range(len(values) - 1))
    monotone_increasing = all(values[i + 1] + 1.0e-10 >= values[i] for i in range(len(values) - 1))
    crossed_down = any(v < threshold for v in values[1:]) and d0 >= threshold
    crossed_up = any(v > threshold for v in values[1:]) and d0 <= threshold
    min_value = min(values)
    max_value = max(values)
    final_value = values[-1]
    final_ratio_to_threshold = final_value / max(threshold, EPS)

    sample_stride = max(1, len(values) // 12)
    samples = [
        {
            "t": times[i],
            "D": values[i],
            "rhs": derivs[i],
        }
        for i in range(0, len(values), sample_stride)
    ]
    if samples[-1]["t"] != times[-1]:
        samples.append({"t": times[-1], "D": values[-1], "rhs": derivs[-1]})

    return {
        "name": name,
        "initial_data": d0,
        "initial_ratio_to_threshold": d0 / max(threshold, EPS),
        "time_horizon": times[-1],
        "step_count": len(values) - 1,
        "dt": dt,
        "final_value": final_value,
        "final_ratio_to_threshold": final_ratio_to_threshold,
        "min_value": min_value,
        "max_value": max_value,
        "initial_rhs": derivs[0],
        "final_rhs": derivs[-1],
        "monotone_decreasing": monotone_decreasing,
        "monotone_increasing": monotone_increasing,
        "crossed_down_below_threshold": crossed_down,
        "crossed_up_above_threshold": crossed_up,
        "hit_cap": hit_cap,
        "depletes_toward_zero": final_value <= max(1.0e-4, 0.1 * threshold),
        "fails_to_deplete": final_value > 0.95 * d0 or final_value > threshold,
        "samples": samples,
    }


def run(args: argparse.Namespace) -> dict[str, Any]:
    threshold = (args.beta / args.big_c) ** (1.0 / args.alpha)
    if args.quick:
        steps = min(args.steps, 1200)
        dt = args.dt
    else:
        steps = args.steps
        dt = args.dt

    good_far = 0.50 * threshold
    good_near = 0.95 * threshold
    bad_near = 1.05 * threshold
    bad_far = 1.50 * threshold

    cases = [
        simulate_case(
            name="good_far_below_threshold",
            d0=good_far,
            beta=args.beta,
            big_c=args.big_c,
            alpha=args.alpha,
            threshold=threshold,
            steps=steps,
            dt=dt,
            cap_multiplier=args.cap_multiplier,
        ),
        simulate_case(
            name="good_near_threshold",
            d0=good_near,
            beta=args.beta,
            big_c=args.big_c,
            alpha=args.alpha,
            threshold=threshold,
            steps=steps,
            dt=dt,
            cap_multiplier=args.cap_multiplier,
        ),
        simulate_case(
            name="bad_near_threshold",
            d0=bad_near,
            beta=args.beta,
            big_c=args.big_c,
            alpha=args.alpha,
            threshold=threshold,
            steps=steps,
            dt=dt,
            cap_multiplier=args.cap_multiplier,
        ),
        simulate_case(
            name="bad_far_above_threshold",
            d0=bad_far,
            beta=args.beta,
            big_c=args.big_c,
            alpha=args.alpha,
            threshold=threshold,
            steps=steps,
            dt=dt,
            cap_multiplier=args.cap_multiplier,
        ),
    ]

    summary = {
        "threshold": threshold,
        "formula": "(beta/C)^(1/alpha)",
        "good_cases_monotone_deplete": all(
            case["monotone_decreasing"] and case["depletes_toward_zero"]
            for case in cases[:2]
        ),
        "bad_cases_fail_to_deplete": all(
            (case["monotone_increasing"] or case["hit_cap"] or case["fails_to_deplete"])
            for case in cases[2:]
        ),
        "below_threshold_rhs_negative": all(case["initial_rhs"] < 0.0 for case in cases[:2]),
        "above_threshold_rhs_positive": all(case["initial_rhs"] > 0.0 for case in cases[2:]),
    }

    return {
        "harness": "ns_a7_residual_depletion_gronwall_harness",
        "scope": "finite_ode_diagnostic_not_ns_clay_proof",
        "ode": {
            "equation": "D' = -beta*D + C*D^(1+alpha)",
            "beta": args.beta,
            "C": args.big_c,
            "alpha": args.alpha,
            "dt": dt,
            "steps": steps,
        },
        "threshold": {
            "value": threshold,
            "formula": "(beta/C)^(1/alpha)",
        },
        "cases": cases,
        "summary": summary,
        "promotion": {
            "a7_proved": False,
            "clay_ns": False,
            "terminal": False,
        },
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--beta", type=float, default=0.4)
    parser.add_argument("--big-c", type=float, default=1.0)
    parser.add_argument("--alpha", type=float, default=0.5)
    parser.add_argument("--dt", type=float, default=0.02)
    parser.add_argument("--steps", type=int, default=4000)
    parser.add_argument("--cap-multiplier", type=float, default=6.0)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output", type=Path)
    return parser.parse_args()


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
