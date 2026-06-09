#!/usr/bin/env python3
"""Kappa arcsine-law diagnostic for the S2 Biot-Savart eigenbundle.

This is a pure-stdlib finite-symbol harness.  It loads
scripts/ns_s2_biot_savart_eigenbundle.py, samples the angular eigenbundle on
S^2, and compares kappa statistics with the exact arcsine reference law

    P(|kappa| < eps) = 2/pi * asin(eps),
    E[kappa^2] = 1/2,
    E[kappa^4] = 3/8.

The primary sample model uses a uniformly random tangent output direction in
span{e_plus(c), omega_hat(c)} and measures its omega_hat component.  A secondary
random-triad proxy measures kappa = <P_c b / |P_c b|, omega_hat(c)> for
c = normalize(a+b), so the same output also records whether raw triad geometry
introduces visible bias.  This is diagnostic evidence only: no PDE, Clay, or
continuum promotion is made here.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import random
import statistics
import sys
from dataclasses import dataclass
from pathlib import Path
from types import ModuleType
from typing import Any, Iterable, Sequence


Vec3 = tuple[float, float, float]

EPS = 1.0e-12
SCRIPT_DIR = Path(__file__).resolve().parent
PROVIDER_PATH = SCRIPT_DIR / "ns_s2_biot_savart_eigenbundle.py"
DEFAULT_EPSILONS = (0.01, 0.02, 0.05, 0.1, 0.2, 1.0 / math.sqrt(2.0), 0.5)


@dataclass(frozen=True)
class SampleSummary:
    name: str
    count: int
    failures: int
    mean: float
    mean_abs: float
    second_moment: float
    fourth_moment: float
    variance: float
    max_abs: float
    moment_errors: dict[str, float]
    abs_cdf: dict[str, dict[str, float]]
    quantiles: dict[str, float]
    clay_promotion: bool


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=20000, help="number of accepted primary samples to target")
    parser.add_argument("--seed", type=int, default=20260608, help="deterministic PRNG seed")
    parser.add_argument("--json", action="store_true", help="emit JSON only")
    parser.add_argument("--json-output", type=Path, help="write compact JSON payload to this path")
    return parser.parse_args(argv)


def load_provider() -> ModuleType:
    if not PROVIDER_PATH.exists():
        raise FileNotFoundError(f"required provider missing: {PROVIDER_PATH}")
    spec = importlib.util.spec_from_file_location("ns_s2_biot_savart_eigenbundle", PROVIDER_PATH)
    if spec is None or spec.loader is None:
        raise ImportError(f"could not load provider spec from {PROVIDER_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def dot(u: Vec3, v: Vec3) -> float:
    return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]


def add(u: Vec3, v: Vec3) -> Vec3:
    return (u[0] + v[0], u[1] + v[1], u[2] + v[2])


def sub(u: Vec3, v: Vec3) -> Vec3:
    return (u[0] - v[0], u[1] - v[1], u[2] - v[2])


def scale(s: float, u: Vec3) -> Vec3:
    return (s * u[0], s * u[1], s * u[2])


def norm_sq(u: Vec3) -> float:
    return dot(u, u)


def norm(u: Vec3) -> float:
    return math.sqrt(max(0.0, norm_sq(u)))


def normalize(u: Vec3, eps: float = EPS) -> Vec3 | None:
    n = norm(u)
    if n <= eps:
        return None
    return scale(1.0 / n, u)


def project(c: Vec3, v: Vec3, eps: float = EPS) -> Vec3 | None:
    c_hat = normalize(c, eps)
    if c_hat is None:
        return None
    return sub(v, scale(dot(v, c_hat), c_hat))


def random_unit(rng: random.Random) -> Vec3:
    z = rng.uniform(-1.0, 1.0)
    theta = rng.uniform(0.0, 2.0 * math.pi)
    r = math.sqrt(max(0.0, 1.0 - z * z))
    return (r * math.cos(theta), r * math.sin(theta), z)


def clamp_unit(x: float) -> float:
    return max(-1.0, min(1.0, x))


def arcsine_abs_cdf(eps: float) -> float:
    if eps < 0.0:
        return 0.0
    if eps >= 1.0:
        return 1.0
    return (2.0 / math.pi) * math.asin(eps)


def quantile(sorted_values: Sequence[float], q: float) -> float:
    if not sorted_values:
        return float("nan")
    if len(sorted_values) == 1:
        return sorted_values[0]
    pos = q * (len(sorted_values) - 1)
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return sorted_values[lo]
    weight = pos - lo
    return sorted_values[lo] * (1.0 - weight) + sorted_values[hi] * weight


def finite_float(x: Any) -> float | None:
    try:
        value = float(x)
    except (TypeError, ValueError):
        return None
    if not math.isfinite(value):
        return None
    return value


def bundle_vectors(provider: ModuleType, c: Vec3) -> tuple[Vec3, Vec3] | None:
    bundle = provider.angular_eigenbundle(c)
    if bundle is None:
        return None
    e_plus_raw = getattr(bundle, "e_plus", None)
    omega_raw = getattr(bundle, "omega_hat", None)
    if not isinstance(e_plus_raw, tuple) or not isinstance(omega_raw, tuple):
        return None
    if len(e_plus_raw) != 3 or len(omega_raw) != 3:
        return None
    e_plus = tuple(finite_float(x) for x in e_plus_raw)
    omega = tuple(finite_float(x) for x in omega_raw)
    if any(x is None for x in e_plus) or any(x is None for x in omega):
        return None
    e_norm = normalize((e_plus[0], e_plus[1], e_plus[2]))  # type: ignore[index]
    o_norm = normalize((omega[0], omega[1], omega[2]))  # type: ignore[index]
    if e_norm is None or o_norm is None:
        return None
    return e_norm, o_norm


def sample_primary_kappas(provider: ModuleType, rng: random.Random, target: int) -> tuple[list[float], int]:
    kappas: list[float] = []
    failures = 0
    attempts = 0
    max_attempts = max(1000, target * 4)
    while len(kappas) < target and attempts < max_attempts:
        attempts += 1
        c = random_unit(rng)
        vectors = bundle_vectors(provider, c)
        if vectors is None:
            failures += 1
            continue
        e_plus, omega = vectors
        theta = rng.uniform(0.0, 2.0 * math.pi)
        tangent_output = add(scale(math.cos(theta), e_plus), scale(math.sin(theta), omega))
        kappas.append(clamp_unit(dot(tangent_output, omega)))
    failures += max(0, target - len(kappas))
    return kappas, failures


def sample_triad_proxy_kappas(provider: ModuleType, rng: random.Random, target: int) -> tuple[list[float], int]:
    kappas: list[float] = []
    failures = 0
    attempts = 0
    max_attempts = max(1000, target * 8)
    while len(kappas) < target and attempts < max_attempts:
        attempts += 1
        a = random_unit(rng)
        b = random_unit(rng)
        c = normalize(add(a, b))
        if c is None:
            failures += 1
            continue
        vectors = bundle_vectors(provider, c)
        pc_b = project(c, b)
        if vectors is None or pc_b is None:
            failures += 1
            continue
        pc_b_hat = normalize(pc_b)
        if pc_b_hat is None:
            failures += 1
            continue
        _e_plus, omega = vectors
        kappas.append(clamp_unit(dot(pc_b_hat, omega)))
    failures += max(0, target - len(kappas))
    return kappas, failures


def summarize(name: str, kappas: Sequence[float], failures: int, epsilons: Iterable[float]) -> SampleSummary:
    if not kappas:
        raise ValueError(f"{name}: no accepted samples")
    n = len(kappas)
    abs_values = [abs(x) for x in kappas]
    sorted_values = sorted(kappas)
    sorted_abs = sorted(abs_values)
    mean = statistics.fmean(kappas)
    mean_abs = statistics.fmean(abs_values)
    second = statistics.fmean(x * x for x in kappas)
    fourth = statistics.fmean(x**4 for x in kappas)
    variance = statistics.fmean((x - mean) ** 2 for x in kappas)

    abs_cdf: dict[str, dict[str, float]] = {}
    for eps in sorted(set(float(x) for x in epsilons)):
        empirical = sum(1 for x in abs_values if x < eps) / n
        expected = arcsine_abs_cdf(eps)
        abs_cdf[f"{eps:.12g}"] = {
            "epsilon": eps,
            "empirical": empirical,
            "arcsine_expected": expected,
            "error": empirical - expected,
            "abs_error": abs(empirical - expected),
        }

    return SampleSummary(
        name=name,
        count=n,
        failures=failures,
        mean=mean,
        mean_abs=mean_abs,
        second_moment=second,
        fourth_moment=fourth,
        variance=variance,
        max_abs=max(abs_values),
        moment_errors={
            "mean_minus_0": mean,
            "mean_abs_minus_2_over_pi": mean_abs - (2.0 / math.pi),
            "second_minus_1_over_2": second - 0.5,
            "fourth_minus_3_over_8": fourth - 0.375,
        },
        abs_cdf=abs_cdf,
        quantiles={
            "q01": quantile(sorted_values, 0.01),
            "q05": quantile(sorted_values, 0.05),
            "q25": quantile(sorted_values, 0.25),
            "q50": quantile(sorted_values, 0.50),
            "q75": quantile(sorted_values, 0.75),
            "q95": quantile(sorted_values, 0.95),
            "q99": quantile(sorted_values, 0.99),
            "abs_q50": quantile(sorted_abs, 0.50),
            "abs_q95": quantile(sorted_abs, 0.95),
        },
        clay_promotion=False,
    )


def summary_to_dict(summary: SampleSummary) -> dict[str, Any]:
    return {
        "name": summary.name,
        "count": summary.count,
        "failures": summary.failures,
        "mean": summary.mean,
        "mean_abs": summary.mean_abs,
        "second_moment": summary.second_moment,
        "fourth_moment": summary.fourth_moment,
        "variance": summary.variance,
        "max_abs": summary.max_abs,
        "moment_errors": summary.moment_errors,
        "abs_cdf": summary.abs_cdf,
        "quantiles": summary.quantiles,
        "clay_promotion": summary.clay_promotion,
    }


def run(samples: int, seed: int) -> dict[str, Any]:
    if samples <= 0:
        raise ValueError("--samples must be positive")
    provider = load_provider()
    rng = random.Random(seed)
    primary, primary_failures = sample_primary_kappas(provider, rng, samples)
    triad_proxy, triad_failures = sample_triad_proxy_kappas(provider, rng, samples)
    summaries = [
        summarize("random_tangent_output", primary, primary_failures, DEFAULT_EPSILONS),
        summarize("random_triad_projected_b_proxy", triad_proxy, triad_failures, DEFAULT_EPSILONS),
    ]
    return {
        "script": "scripts/ns_kappa_arcsine_law_harness.py",
        "theorem_label": "NS-F3",
        "theorem_name": "NSCascadeKappaArcsineLaw",
        "provider": str(PROVIDER_PATH),
        "seed": seed,
        "requested_samples": samples,
        "scope": "finite_s2_biot_savart_symbol_diagnostic_not_pde_proof",
        "exact_constants": {
            "density": "1/(pi*sqrt(1-kappa^2))",
            "mean": 0.0,
            "mean_abs": 2.0 / math.pi,
            "second_moment": 0.5,
            "fourth_moment": 0.375,
            "coherent_fraction": "P(|kappa|<eps)=2/pi*asin(eps)",
        },
        "reference_law": {
            "name": "arcsine_on_minus_one_one",
            "density": "1/(pi*sqrt(1-kappa^2))",
            "abs_cdf": "P(|kappa|<eps)=2/pi*asin(eps)",
            "second_moment": 0.5,
            "fourth_moment": 0.375,
            "mean_abs": 2.0 / math.pi,
        },
        "summaries": {summary.name: summary_to_dict(summary) for summary in summaries},
        "promotion": {
            "finite_statistical_diagnostic": True,
            "pde_or_clay_promotion": False,
            "terminal_promotion": False,
        },
        "promotion_false": True,
        "clay_promotion": False,
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    result = run(args.samples, args.seed)
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        with args.json_output.open("w", encoding="utf-8") as handle:
            json.dump(result, handle, sort_keys=True, separators=(",", ":"))
            handle.write("\n")
    if args.json:
        print(json.dumps(result, sort_keys=True, separators=(",", ":")))
    else:
        print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
