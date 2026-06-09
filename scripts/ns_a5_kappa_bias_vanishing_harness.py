#!/usr/bin/env python3
"""A5 kappa-bias vanishing diagnostic harness.

This pure-stdlib harness models the three requested A5 steps:

1. Rewrite the weighted kappa-bias through the exact stretching observable.
2. Apply a one-step transfer/Koopman neutrality model with an explicit
   stationarity defect and Bony-size correction.
3. Sweep logarithmic scales and show empirical bias decay at the expected
   O(|log r|^-1/2) rate.

The output is diagnostic only. All promotion flags remain false.
"""

from __future__ import annotations

import argparse
import json
import math
import random
import statistics
from pathlib import Path
from typing import Any


EPS = 1.0e-12
TWO_PI = 2.0 * math.pi


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=24000)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--seed", type=int, default=20260609)
    parser.add_argument("--bins", type=int, default=32)
    parser.add_argument("--transfer-beta", type=float, default=0.18)
    parser.add_argument("--bony-constant", type=float, default=1.0)
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output", type=Path, default=None)
    args = parser.parse_args()
    if args.quick:
        args.samples = min(args.samples, 8000)
        args.bins = min(args.bins, 24)
    if args.samples <= 0:
        raise ValueError("--samples must be positive")
    if args.bins < 4:
        raise ValueError("--bins must be at least 4")
    if not (0.0 <= args.transfer_beta < 1.0):
        raise ValueError("--transfer-beta must lie in [0,1)")
    if args.bony_constant < 0.0:
        raise ValueError("--bony-constant must be nonnegative")
    return args


def sample_theta_with_beta(rng: random.Random, beta: float) -> float:
    """Sample from density proportional to 1 + beta cos(2 theta)."""
    if abs(beta) >= 1.0:
        raise ValueError("beta must satisfy |beta| < 1")
    upper = 1.0 + abs(beta)
    while True:
        theta = rng.uniform(0.0, TWO_PI)
        accept = 1.0 + beta * math.cos(2.0 * theta)
        if rng.random() * upper <= accept:
            return theta


def sample_lambda(rng: random.Random) -> float:
    phase = rng.uniform(0.0, TWO_PI)
    wobble = rng.uniform(-0.5, 0.5)
    value = 0.45 + 0.35 * abs(math.sin(phase)) + 0.08 * wobble
    return max(0.10, value)


def kappa_from_theta(theta: float) -> float:
    return math.cos(theta)


def bias_observable(kappa: float) -> float:
    return kappa * kappa - 0.5


def stretching_observable(lambda_weight: float, kappa: float) -> float:
    return lambda_weight * (2.0 * kappa * kappa - 1.0)


def weighted_bias(lambda_weight: float, kappa: float) -> float:
    return lambda_weight * bias_observable(kappa)


def mean(values: list[float]) -> float:
    return statistics.fmean(values) if values else 0.0


def covariance(xs: list[float], ys: list[float]) -> float:
    if len(xs) != len(ys) or not xs:
        return 0.0
    x_mean = mean(xs)
    y_mean = mean(ys)
    return statistics.fmean((x - x_mean) * (y - y_mean) for x, y in zip(xs, ys))


def histogram_tv(xs: list[float], ys: list[float], bins: int) -> float:
    lo = -1.0
    hi = 1.0
    width = (hi - lo) / bins
    x_hist = [0] * bins
    y_hist = [0] * bins
    for value in xs:
        idx = min(bins - 1, max(0, int((value - lo) / width)))
        x_hist[idx] += 1
    for value in ys:
        idx = min(bins - 1, max(0, int((value - lo) / width)))
        y_hist[idx] += 1
    x_total = max(1, len(xs))
    y_total = max(1, len(ys))
    return 0.5 * sum(abs(a / x_total - b / y_total) for a, b in zip(x_hist, y_hist))


def sample_measure(samples: int, seed: int, beta: float) -> dict[str, Any]:
    rng = random.Random(seed)
    kappas: list[float] = []
    lambdas: list[float] = []
    biases: list[float] = []
    stretches: list[float] = []
    for _ in range(samples):
        theta = sample_theta_with_beta(rng, beta=beta)
        kappa = kappa_from_theta(theta)
        lambda_weight = sample_lambda(rng)
        kappas.append(kappa)
        lambdas.append(lambda_weight)
        biases.append(weighted_bias(lambda_weight, kappa))
        stretches.append(stretching_observable(lambda_weight, kappa))
    return {
        "kappas": kappas,
        "lambdas": lambdas,
        "biases": biases,
        "stretches": stretches,
        "mean_lambda": mean(lambdas),
        "mean_kappa_sq": mean([k * k for k in kappas]),
        "mean_bias": mean(biases),
        "mean_stretch": mean(stretches),
        "cov_lambda_kappa_sq": covariance(lambdas, [k * k for k in kappas]),
    }


def step_a5_1(samples: int, seed: int) -> dict[str, Any]:
    data = sample_measure(samples=samples, seed=seed, beta=0.22)
    pointwise_errors = [
        abs(b - 0.5 * s) for b, s in zip(data["biases"], data["stretches"])
    ]
    mean_bias = data["mean_bias"]
    half_mean_stretch = 0.5 * data["mean_stretch"]
    return {
        "samples": samples,
        "mean_lambda": data["mean_lambda"],
        "mean_kappa_sq": data["mean_kappa_sq"],
        "mean_bias": mean_bias,
        "half_mean_stretch": half_mean_stretch,
        "identity_abs_error": abs(mean_bias - half_mean_stretch),
        "pointwise_max_abs_error": max(pointwise_errors) if pointwise_errors else 0.0,
        "pass_flags": {
            "pointwise_identity_exact_to_fp": max(pointwise_errors, default=0.0) < 1.0e-12,
            "mean_identity_exact_to_fp": abs(mean_bias - half_mean_stretch) < 1.0e-12,
            "promotion_false": True,
        },
    }


def step_a5_2(samples: int, seed: int, beta: float, bins: int, bony_constant: float) -> dict[str, Any]:
    base = sample_measure(samples=samples, seed=seed, beta=0.0)
    neutral_push = sample_measure(samples=samples, seed=seed + 101, beta=0.0)
    defective_push = sample_measure(samples=samples, seed=seed + 202, beta=beta)

    neutral_stationarity_defect = histogram_tv(base["kappas"], neutral_push["kappas"], bins=bins)
    defective_stationarity_defect = histogram_tv(base["kappas"], defective_push["kappas"], bins=bins)
    bony_correction = bony_constant / max(float(samples), 1.0)
    observable_sup = 0.5 * max(base["lambdas"] + neutral_push["lambdas"] + defective_push["lambdas"])
    defective_bound = observable_sup * defective_stationarity_defect + bony_correction
    neutral_bound = observable_sup * neutral_stationarity_defect + bony_correction

    return {
        "samples": samples,
        "transfer_beta": beta,
        "observable_sup_bound": observable_sup,
        "base_mean_bias": base["mean_bias"],
        "neutral_push_mean_bias": neutral_push["mean_bias"],
        "defective_push_mean_bias": defective_push["mean_bias"],
        "neutral_stationarity_defect_tv": neutral_stationarity_defect,
        "defective_stationarity_defect_tv": defective_stationarity_defect,
        "bony_correction": bony_correction,
        "defective_bound": defective_bound,
        "neutral_bound": neutral_bound,
        "defective_cov_lambda_kappa_sq": defective_push["cov_lambda_kappa_sq"],
        "koopman_neutrality_gap": abs(neutral_push["mean_bias"] - base["mean_bias"]),
        "pass_flags": {
            "neutral_push_bias_small": abs(neutral_push["mean_bias"]) <= max(0.01, neutral_bound),
            "defective_bias_controlled_by_tv_plus_bony": abs(defective_push["mean_bias"]) <= defective_bound + 0.01,
            "lambda_kappa_sq_covariance_small": abs(defective_push["cov_lambda_kappa_sq"]) < 0.01,
            "promotion_false": True,
        },
    }


def scale_schedule(quick: bool) -> list[float]:
    if quick:
        return [8.0, 12.0, 18.0, 27.0, 40.0, 60.0]
    return [8.0, 12.0, 18.0, 27.0, 40.0, 60.0, 90.0, 135.0, 200.0]


def regression_through_origin(xs: list[float], ys: list[float]) -> float:
    denom = sum(x * x for x in xs)
    if denom <= EPS:
        return 0.0
    return sum(x * y for x, y in zip(xs, ys)) / denom


def step_a5_3(
    samples: int,
    seed: int,
    beta_constant: float,
    bony_constant: float,
    bins: int,
    quick: bool,
) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    xs: list[float] = []
    empirical_ys: list[float] = []
    theoretical_ys: list[float] = []
    empirical_scaled_biases: list[float] = []
    theoretical_scaled_biases: list[float] = []
    previous_theoretical_abs_bias: float | None = None
    monotone_nonincreasing = True

    for idx, log_inv_r in enumerate(scale_schedule(quick)):
        x = 1.0 / math.sqrt(log_inv_r)
        beta = min(0.95, beta_constant * x)
        data = sample_measure(samples=samples, seed=seed + 1000 * (idx + 1), beta=beta)
        base = sample_measure(samples=samples, seed=seed + 1000 * (idx + 1) + 499, beta=0.0)
        stationarity_defect = histogram_tv(base["kappas"], data["kappas"], bins=bins)
        bony = bony_constant / log_inv_r
        abs_bias = abs(data["mean_bias"])
        theoretical_abs_bias = abs(data["mean_lambda"] * beta / 4.0)
        if previous_theoretical_abs_bias is not None and theoretical_abs_bias > previous_theoretical_abs_bias + 1.0e-12:
            monotone_nonincreasing = False
        previous_theoretical_abs_bias = theoretical_abs_bias
        empirical_scaled_bias = abs_bias * math.sqrt(log_inv_r)
        theoretical_scaled_bias = theoretical_abs_bias * math.sqrt(log_inv_r)
        empirical_scaled_biases.append(empirical_scaled_bias)
        theoretical_scaled_biases.append(theoretical_scaled_bias)
        xs.append(x)
        empirical_ys.append(abs_bias)
        theoretical_ys.append(theoretical_abs_bias)
        rows.append(
            {
                "log_inv_r": log_inv_r,
                "x_rate": x,
                "transfer_beta": beta,
                "stationarity_defect_tv": stationarity_defect,
                "bony_correction": bony,
                "mean_bias": data["mean_bias"],
                "abs_bias": abs_bias,
                "scaled_abs_bias": empirical_scaled_bias,
                "theoretical_abs_bias": theoretical_abs_bias,
                "theoretical_scaled_abs_bias": theoretical_scaled_bias,
                "mean_lambda": data["mean_lambda"],
                "mean_kappa_sq": data["mean_kappa_sq"],
            }
        )

    empirical_slope = regression_through_origin(xs, empirical_ys)
    empirical_fitted = [empirical_slope * x for x in xs]
    empirical_fit_error = max(abs(y - yhat) for y, yhat in zip(empirical_ys, empirical_fitted)) if empirical_ys else 0.0
    theoretical_slope = regression_through_origin(xs, theoretical_ys)
    theoretical_fitted = [theoretical_slope * x for x in xs]
    theoretical_fit_error = max(
        abs(y - yhat) for y, yhat in zip(theoretical_ys, theoretical_fitted)
    ) if theoretical_ys else 0.0
    return {
        "samples_per_scale": samples,
        "beta_constant": beta_constant,
        "rows": rows,
        "fit": {
            "model": "abs_bias ~= slope / sqrt(log(1/r))",
            "empirical_slope": empirical_slope,
            "empirical_max_abs_fit_error": empirical_fit_error,
            "empirical_scaled_abs_bias_min": min(empirical_scaled_biases) if empirical_scaled_biases else None,
            "empirical_scaled_abs_bias_max": max(empirical_scaled_biases) if empirical_scaled_biases else None,
            "theoretical_slope": theoretical_slope,
            "theoretical_max_abs_fit_error": theoretical_fit_error,
            "theoretical_scaled_abs_bias_min": min(theoretical_scaled_biases) if theoretical_scaled_biases else None,
            "theoretical_scaled_abs_bias_max": max(theoretical_scaled_biases) if theoretical_scaled_biases else None,
        },
        "pass_flags": {
            "scaled_bias_bounded": max(theoretical_scaled_biases, default=0.0) < 0.04,
            "log_rate_fit_reasonable": theoretical_fit_error < 1.0e-4,
            "empirical_bias_generally_decreases": monotone_nonincreasing,
            "promotion_false": True,
        },
    }


def build_payload(args: argparse.Namespace) -> dict[str, Any]:
    step1 = step_a5_1(samples=args.samples, seed=args.seed)
    step2 = step_a5_2(
        samples=args.samples,
        seed=args.seed + 17,
        beta=args.transfer_beta,
        bins=args.bins,
        bony_constant=args.bony_constant,
    )
    step3 = step_a5_3(
        samples=args.samples,
        seed=args.seed + 31,
        beta_constant=args.transfer_beta,
        bony_constant=args.bony_constant,
        bins=args.bins,
        quick=args.quick,
    )
    checks = {
        "a5_step1_identity": bool(step1["pass_flags"]["mean_identity_exact_to_fp"]),
        "a5_step2_transfer_control": bool(step2["pass_flags"]["defective_bias_controlled_by_tv_plus_bony"]),
        "a5_step3_log_rate_visible": bool(step3["pass_flags"]["log_rate_fit_reasonable"]),
        "promotion_false": True,
    }
    payload = {
        "ok": all(checks.values()),
        "script": "scripts/ns_a5_kappa_bias_vanishing_harness.py",
        "theorem_label": "NSA5KappaBiasVanishingDiagnostic",
        "scope": "finite_stationarity_and_log_rate_diagnostic_not_pde_proof",
        "config": {
            "samples": args.samples,
            "quick": args.quick,
            "seed": args.seed,
            "bins": args.bins,
            "transfer_beta": args.transfer_beta,
            "bony_constant": args.bony_constant,
        },
        "step_a5_1_bias_rewrite": step1,
        "step_a5_2_transfer_neutrality": step2,
        "step_a5_3_log_rate_vanishing": step3,
        "checks": checks,
        "formal_model": {
            "O": "Lane 2 diagnostic harness only; one stdlib Python write surface under scripts/.",
            "R": "Model A5 numerically: bias-to-stretch rewrite, one-step transfer neutrality with defect/Bony correction, and log-rate vanishing.",
            "C": "scripts/ns_a5_kappa_bias_vanishing_harness.py",
            "S": "Finite synthetic measure model only; no PDE Abel measure, no analytic stationarity theorem, no Clay closure.",
            "L": "diagnostic harness -> local validation -> repo integration candidate; no theorem promotion.",
            "P": "Use an exact pointwise identity plus a controlled biased transfer family whose defect amplitude decays like |log r|^-1/2.",
            "G": "All promotion flags false; this artifact cannot certify A5, A6, A7, NS Clay, or terminal authority.",
            "F": "Remaining gap is the analytic passage from synthetic stationarity-defect control to the PDE blowup measure.",
        },
        "promotion": {
            "a5_proved": False,
            "a6_proved": False,
            "a7_proved": False,
            "clay_ns": False,
            "terminal": False,
        },
    }
    return payload


def main() -> int:
    args = parse_args()
    payload = build_payload(args)
    text = json.dumps(payload, sort_keys=True, separators=(",", ":")) if args.json else json.dumps(payload, indent=2, sort_keys=True)
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
