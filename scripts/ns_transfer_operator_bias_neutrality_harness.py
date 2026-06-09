#!/usr/bin/env python3
"""Transfer-operator kappa-bias neutrality smoke harness.

This pure-stdlib diagnostic samples

    kappa = cos(theta),  theta ~ Uniform[0, 2*pi)

and checks the finite statistical identity

    E[lambda * (kappa^2 - 1/2)] / E[lambda] = 0

when lambda is sampled independently from kappa.  It also includes a
deliberately correlated counterexample, where lambda is larger on high
|kappa| samples, so the conditional-independence assumption is visible in the
JSON output.  This is a finite smoke test only and makes no PDE or Clay
promotion.
"""

from __future__ import annotations

import argparse
import json
import math
import random
import statistics
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence


DEFAULT_OUTPUT = Path("outputs/ns_transfer_operator_bias_neutrality_summary.json")
EPS = 1.0e-12


@dataclass(frozen=True)
class Row:
    kappa: float
    lambda_weight: float
    bias_observable: float
    weighted_bias: float


@dataclass(frozen=True)
class Summary:
    regime: str
    samples: int
    mean_kappa: float
    mean_kappa_sq: float
    unweighted_bias_mean: float
    mean_lambda: float
    pushforward_mean_bias: float
    covariance_lambda_bias_observable: float
    positive_weight_fraction: float
    lambda_min: float
    lambda_max: float
    lambda_q05: float
    lambda_q50: float
    lambda_q95: float
    pass_flags: dict[str, bool]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=20000)
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true")
    return parser.parse_args(argv)


def quantile(sorted_values: Sequence[float], q: float) -> float:
    if not sorted_values:
        raise ValueError("quantile requires at least one value")
    if len(sorted_values) == 1:
        return sorted_values[0]
    position = q * (len(sorted_values) - 1)
    lo = int(math.floor(position))
    hi = int(math.ceil(position))
    if lo == hi:
        return sorted_values[lo]
    weight = position - lo
    return sorted_values[lo] * (1.0 - weight) + sorted_values[hi] * weight


def sample_lambda_independent(rng: random.Random) -> float:
    # Smooth positive local transfer weight, independent from theta/kappa.
    phase = rng.uniform(0.0, 2.0 * math.pi)
    jitter = rng.random()
    return 1.0 + 0.20 * math.cos(phase) + 0.05 * (jitter - 0.5)


def sample_lambda_correlated(kappa: float) -> float:
    # Deliberately violates conditional independence: high |kappa| gets larger
    # transfer mass and therefore positive kappa^2 - 1/2 bias.
    kappa_sq = kappa * kappa
    return 1.0 + 2.50 * kappa_sq


def build_rows(regime: str, samples: int, seed: int) -> list[Row]:
    if samples <= 0:
        raise ValueError("--samples must be positive")
    rng = random.Random(seed)
    rows: list[Row] = []
    for _ in range(samples):
        theta = rng.uniform(0.0, 2.0 * math.pi)
        kappa = math.cos(theta)
        bias_observable = kappa * kappa - 0.5
        if regime == "independent_lambda_neutral":
            lambda_weight = sample_lambda_independent(rng)
        elif regime == "correlated_lambda_counterexample":
            lambda_weight = sample_lambda_correlated(kappa)
        else:
            raise ValueError(f"unknown regime: {regime}")
        rows.append(
            Row(
                kappa=kappa,
                lambda_weight=lambda_weight,
                bias_observable=bias_observable,
                weighted_bias=lambda_weight * bias_observable,
            )
        )
    return rows


def covariance(xs: Sequence[float], ys: Sequence[float]) -> float:
    if len(xs) != len(ys):
        raise ValueError("covariance inputs must have the same length")
    if not xs:
        raise ValueError("covariance requires at least one value")
    x_mean = statistics.fmean(xs)
    y_mean = statistics.fmean(ys)
    return statistics.fmean((x - x_mean) * (y - y_mean) for x, y in zip(xs, ys))


def summarize(regime: str, rows: Sequence[Row]) -> Summary:
    if not rows:
        raise ValueError(f"{regime}: no rows")
    kappas = [row.kappa for row in rows]
    kappa_sq = [row.kappa * row.kappa for row in rows]
    bias_observables = [row.bias_observable for row in rows]
    lambdas = [row.lambda_weight for row in rows]
    sorted_lambdas = sorted(lambdas)
    mean_lambda = statistics.fmean(lambdas)
    if mean_lambda <= EPS:
        raise ValueError(f"{regime}: nonpositive mean lambda")
    pushforward_mean_bias = statistics.fmean(row.weighted_bias for row in rows) / mean_lambda

    if regime == "independent_lambda_neutral":
        pass_flags = {
            "mean_kappa_sq_near_half": abs(statistics.fmean(kappa_sq) - 0.5) < 0.01,
            "pushforward_mean_bias_near_zero": abs(pushforward_mean_bias) < 0.01,
            "lambda_bias_covariance_small": abs(covariance(lambdas, bias_observables)) < 0.003,
            "promotion_false": True,
        }
    else:
        pass_flags = {
            "counterexample_bias_visible": pushforward_mean_bias > 0.10,
            "lambda_bias_covariance_positive": covariance(lambdas, bias_observables) > 0.10,
            "promotion_false": True,
        }

    return Summary(
        regime=regime,
        samples=len(rows),
        mean_kappa=statistics.fmean(kappas),
        mean_kappa_sq=statistics.fmean(kappa_sq),
        unweighted_bias_mean=statistics.fmean(bias_observables),
        mean_lambda=mean_lambda,
        pushforward_mean_bias=pushforward_mean_bias,
        covariance_lambda_bias_observable=covariance(lambdas, bias_observables),
        positive_weight_fraction=sum(1 for item in lambdas if item > 0.0) / len(lambdas),
        lambda_min=min(lambdas),
        lambda_max=max(lambdas),
        lambda_q05=quantile(sorted_lambdas, 0.05),
        lambda_q50=quantile(sorted_lambdas, 0.50),
        lambda_q95=quantile(sorted_lambdas, 0.95),
        pass_flags=pass_flags,
    )


def run(samples: int, seed: int) -> dict[str, object]:
    regimes = (
        "independent_lambda_neutral",
        "correlated_lambda_counterexample",
    )
    summaries: dict[str, dict[str, object]] = {}
    for index, regime in enumerate(regimes):
        rows = build_rows(regime=regime, samples=samples, seed=seed + 1009 * index)
        summaries[regime] = asdict(summarize(regime, rows))

    checks = {
        "independent_pushforward_bias_near_zero": bool(
            summaries["independent_lambda_neutral"]["pass_flags"]["pushforward_mean_bias_near_zero"]  # type: ignore[index]
        ),
        "correlated_counterexample_visible": bool(
            summaries["correlated_lambda_counterexample"]["pass_flags"]["counterexample_bias_visible"]  # type: ignore[index]
        ),
        "promotion_false": True,
    }

    return {
        "ok": all(checks.values()),
        "script": "scripts/ns_transfer_operator_bias_neutrality_harness.py",
        "theorem_label": "NS-transfer-operator-bias-neutrality",
        "seed": seed,
        "requested_samples_per_regime": samples,
        "scope": "finite_arcsine_kappa_statistical_identity_not_pde_proof",
        "identity": {
            "kappa": "cos(theta), theta independent uniform on [0,2*pi)",
            "bias_observable": "kappa^2 - 1/2",
            "neutrality_condition": "lambda independent from kappa",
            "pushforward_mean_bias": "E[lambda*(kappa^2-1/2)]/E[lambda]",
        },
        "summaries": summaries,
        "checks": checks,
        "promotion": {
            "finite_statistical_diagnostic": True,
            "transfer_operator_assumption_tested": "conditional independence of lambda from kappa",
            "pde_or_clay_promotion": False,
            "terminal_promotion": False,
        },
        "promotion_false": True,
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    payload = run(samples=args.samples, seed=args.seed)
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    with args.json_output.open("w", encoding="utf-8") as handle:
        json.dump(payload, handle, sort_keys=True, separators=(",", ":"))
        handle.write("\n")
    if args.json:
        print(json.dumps(payload, sort_keys=True, separators=(",", ":")))
    else:
        print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
