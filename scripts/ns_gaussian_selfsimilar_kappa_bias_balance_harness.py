#!/usr/bin/env python3
"""Corrected Gaussian self-similar kappa-bias balance diagnostic.

This pure-stdlib harness probes the normalized balance

    nontrivial self-similar profile requires 1 <= 4*bias + drift

where bias is a Gaussian/strain-weighted proxy for

    integral lambda(c) * (kappa^2 - 1/2) dmu

and drift is the normalized nonlinear sweeping correction.  The calculation is
diagnostic only: it does not construct an Abel triadic defect measure, does not
prove a Type-I blowup exclusion theorem, and does not promote NS/Clay.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import random
import statistics
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from types import ModuleType
from typing import Any, Sequence


Vec3 = tuple[float, float, float]

SCRIPT_DIR = Path(__file__).resolve().parent
PROVIDER_PATH = SCRIPT_DIR / "ns_s2_biot_savart_eigenbundle.py"
DEFAULT_OUTPUT = Path("outputs/ns_gaussian_selfsimilar_kappa_bias_balance_summary.json")
EPS = 1.0e-12
REGIMES = (
    "neutral_arcsine_NRS",
    "stationary_proxy",
    "biased_counterexample",
    "drift_dominated",
)


@dataclass(frozen=True)
class Shell:
    index: int
    radius: float
    gaussian_weight: float
    amplitude: float
    amplitude_slope: float
    normalized_diffusion: float


@dataclass(frozen=True)
class Row:
    regime: str
    shell_index: int
    lambda_weight: float
    kappa: float
    strain_bias: float
    gaussian_weight: float
    enstrophy_weight: float
    drift_density: float


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=10000)
    parser.add_argument("--shells", type=int, default=14)
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--json", action="store_true")
    return parser.parse_args(argv)


def dot(u: Vec3, v: Vec3) -> float:
    return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]


def scale(scalar: float, u: Vec3) -> Vec3:
    return (scalar * u[0], scalar * u[1], scalar * u[2])


def norm(u: Vec3) -> float:
    return math.sqrt(max(0.0, dot(u, u)))


def normalize(u: Vec3, eps: float = EPS) -> Vec3 | None:
    size = norm(u)
    if size <= eps:
        return None
    return scale(1.0 / size, u)


def random_unit(rng: random.Random) -> Vec3:
    z = rng.uniform(-1.0, 1.0)
    theta = rng.uniform(0.0, 2.0 * math.pi)
    radius = math.sqrt(max(0.0, 1.0 - z * z))
    return (radius * math.cos(theta), radius * math.sin(theta), z)


def coerce_vec3(value: Any) -> Vec3 | None:
    if not isinstance(value, (tuple, list)) or len(value) != 3:
        return None
    try:
        out = (float(value[0]), float(value[1]), float(value[2]))
    except (TypeError, ValueError):
        return None
    if not all(math.isfinite(item) for item in out):
        return None
    return out


def load_provider() -> ModuleType:
    if not PROVIDER_PATH.exists():
        raise FileNotFoundError(f"required provider missing: {PROVIDER_PATH}")
    spec = importlib.util.spec_from_file_location("ns_s2_biot_savart_eigenbundle", PROVIDER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"failed to load provider spec: {PROVIDER_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def lambda_weight(provider: ModuleType, c: Vec3) -> float | None:
    bundle = provider.angular_eigenbundle(c, EPS)
    if bundle is None:
        return None
    omega_hat = normalize(coerce_vec3(getattr(bundle, "omega_hat", None)) or (0.0, 0.0, 0.0))
    if omega_hat is None:
        return None
    m11 = float(getattr(bundle, "m11"))
    m12 = float(getattr(bundle, "m12"))
    value = math.hypot(m11, m12)
    if not math.isfinite(value):
        return None
    return value


def profile_amplitude(radius: float) -> float:
    # A smooth Type-I-like shell envelope.  It is a diagnostic weighting model,
    # not a PDE solution.
    log_radius = math.log(radius)
    return math.exp(-0.30 * log_radius * log_radius) / math.sqrt(1.0 + 0.05 * radius * radius)


def build_shells(count: int) -> list[Shell]:
    if count < 3:
        raise ValueError("--shells must be at least 3")
    log_min = math.log(0.35)
    log_max = math.log(2.8)
    logs = [log_min + (log_max - log_min) * index / (count - 1) for index in range(count)]
    radii = [math.exp(item) for item in logs]
    amplitudes = [profile_amplitude(radius) for radius in radii]
    slopes: list[float] = []
    for index in range(count):
        if index == 0:
            slope = (math.log(amplitudes[1]) - math.log(amplitudes[0])) / (logs[1] - logs[0])
        elif index == count - 1:
            slope = (math.log(amplitudes[-1]) - math.log(amplitudes[-2])) / (logs[-1] - logs[-2])
        else:
            slope = (math.log(amplitudes[index + 1]) - math.log(amplitudes[index - 1])) / (
                logs[index + 1] - logs[index - 1]
            )
        slopes.append(slope)

    max_radius_sq = max(radius * radius for radius in radii)
    return [
        Shell(
            index=index,
            radius=radius,
            gaussian_weight=math.exp(-0.25 * radius * radius),
            amplitude=amplitudes[index],
            amplitude_slope=slopes[index],
            normalized_diffusion=(radius * radius) / max_radius_sq,
        )
        for index, radius in enumerate(radii)
    ]


def choose_shell(rng: random.Random, shells: Sequence[Shell]) -> Shell:
    weights = [shell.gaussian_weight * shell.amplitude * shell.amplitude for shell in shells]
    total = sum(weights)
    if total <= EPS:
        return shells[rng.randrange(len(shells))]
    threshold = rng.random() * total
    running = 0.0
    for shell, weight in zip(shells, weights):
        running += weight
        if running >= threshold:
            return shell
    return shells[-1]


def arcsine_kappa(rng: random.Random) -> float:
    return math.cos(rng.uniform(0.0, 2.0 * math.pi))


def regime_kappa(regime: str, shell: Shell, rng: random.Random) -> float:
    if regime == "neutral_arcsine_NRS":
        return arcsine_kappa(rng)
    if regime == "stationary_proxy":
        # Stationary transport damps high-|kappa| excess toward the arcsine
        # neutral baseline and leaves a mild compressive tilt.
        base = arcsine_kappa(rng)
        tilt = 0.88 - 0.08 * shell.normalized_diffusion
        return max(-1.0, min(1.0, tilt * base))
    if regime == "biased_counterexample":
        # Deliberately concentrate in the stretching half |kappa|>1/sqrt(2).
        sign = -1.0 if rng.random() < 0.5 else 1.0
        u = rng.random()
        return sign * math.sqrt(0.5 + 0.5 * (1.0 - u * u))
    if regime == "drift_dominated":
        return arcsine_kappa(rng)
    raise ValueError(f"unknown regime: {regime}")


def regime_drift_density(regime: str, shell: Shell, rng: random.Random) -> float:
    if regime == "neutral_arcsine_NRS":
        return 0.0
    if regime == "stationary_proxy":
        return 0.18 * shell.amplitude_slope
    if regime == "biased_counterexample":
        return 0.05 * shell.amplitude_slope
    if regime == "drift_dominated":
        # This is an intentionally artificial sweeping-dominated regime that
        # satisfies the balance without positive kappa bias.
        return 1.18 + 0.06 * rng.random()
    raise ValueError(f"unknown regime: {regime}")


def sample_rows(provider: ModuleType, regime: str, samples: int, shells: Sequence[Shell], seed: int) -> list[Row]:
    rng = random.Random(seed)
    rows: list[Row] = []
    attempts = 0
    max_attempts = max(samples * 4, samples + 100)
    while len(rows) < samples and attempts < max_attempts:
        attempts += 1
        shell = choose_shell(rng, shells)
        value = lambda_weight(provider, random_unit(rng))
        if value is None:
            continue
        kappa = regime_kappa(regime, shell, rng)
        enstrophy_weight = shell.gaussian_weight * shell.amplitude * shell.amplitude
        rows.append(
            Row(
                regime=regime,
                shell_index=shell.index,
                lambda_weight=value,
                kappa=kappa,
                strain_bias=value * (kappa * kappa - 0.5),
                gaussian_weight=shell.gaussian_weight,
                enstrophy_weight=enstrophy_weight,
                drift_density=regime_drift_density(regime, shell, rng),
            )
        )
    if len(rows) < samples:
        raise RuntimeError(f"{regime}: accepted only {len(rows)}/{samples} samples")
    return rows


def weighted_mean(pairs: Sequence[tuple[float, float]]) -> float:
    total_weight = sum(weight for _, weight in pairs)
    if total_weight <= EPS:
        raise ValueError("zero total weight")
    return sum(value * weight for value, weight in pairs) / total_weight


def quantile(values: Sequence[float], q: float) -> float | None:
    finite = sorted(value for value in values if math.isfinite(value))
    if not finite:
        return None
    index = min(len(finite) - 1, max(0, int(round(q * (len(finite) - 1)))))
    return finite[index]


def summarize_regime(regime: str, rows: Sequence[Row]) -> dict[str, object]:
    bias = weighted_mean([(row.strain_bias, row.enstrophy_weight) for row in rows])
    mean_lambda = weighted_mean([(row.lambda_weight, row.enstrophy_weight) for row in rows])
    normalized_bias = bias / mean_lambda if mean_lambda > EPS else 0.0
    drift = weighted_mean([(row.drift_density, row.enstrophy_weight) for row in rows])
    rhs = 4.0 * normalized_bias + drift
    kappa_sq = [row.kappa * row.kappa for row in rows]
    lhs_lower_bound = 1.0
    nontrivial_balance_satisfied = rhs >= lhs_lower_bound
    contradiction_with_nontrivial = not nontrivial_balance_satisfied

    return {
        "regime": regime,
        "accepted_samples": len(rows),
        "mean_lambda": mean_lambda,
        "weighted_bias": bias,
        "normalized_bias": normalized_bias,
        "drift": drift,
        "balance_rhs_4_bias_plus_drift": rhs,
        "balance_lhs_lower_bound": lhs_lower_bound,
        "nontrivial_balance_satisfied": nontrivial_balance_satisfied,
        "contradiction_with_nontrivial": contradiction_with_nontrivial,
        "mean_kappa_sq": statistics.fmean(kappa_sq),
        "kappa_sq_p05": quantile(kappa_sq, 0.05),
        "kappa_sq_p50": quantile(kappa_sq, 0.50),
        "kappa_sq_p95": quantile(kappa_sq, 0.95),
        "positive_pointwise_bias_fraction": sum(1 for row in rows if row.strain_bias > 0.0) / len(rows),
        "pass_flags": {
            "diagnostic_completed": True,
            "inequality_evaluated": True,
            "promotion_false": True,
        },
    }


def run(samples: int, shells_count: int, seed: int) -> dict[str, object]:
    if samples <= 0:
        raise ValueError("--samples must be positive")
    provider = load_provider()
    shells = build_shells(shells_count)
    regimes: dict[str, dict[str, object]] = {}
    for index, regime in enumerate(REGIMES):
        rows = sample_rows(provider, regime, samples, shells, seed + 1009 * index)
        regimes[regime] = summarize_regime(regime, rows)

    neutral = regimes["neutral_arcsine_NRS"]
    stationary = regimes["stationary_proxy"]
    biased = regimes["biased_counterexample"]
    drift_dominated = regimes["drift_dominated"]

    checks = {
        "neutral_arcsine_NRS_recovers_NRS_contradiction_proxy": bool(
            neutral["contradiction_with_nontrivial"] and abs(float(neutral["normalized_bias"])) < 0.03
        ),
        "stationary_proxy_kills_positive_balance": bool(stationary["contradiction_with_nontrivial"]),
        "biased_counterexample_can_satisfy_balance": bool(biased["nontrivial_balance_satisfied"]),
        "drift_dominated_can_satisfy_balance_without_bias": bool(
            drift_dominated["nontrivial_balance_satisfied"] and float(drift_dominated["normalized_bias"]) < 0.05
        ),
        "promotion_false": True,
        "diagnostic_only": True,
    }

    return {
        "ok": all(checks.values()),
        "harness": "ns_gaussian_selfsimilar_kappa_bias_balance_harness",
        "scope": "corrected_gaussian_balance_proxy_not_pde_proof",
        "provider": str(PROVIDER_PATH),
        "seed": seed,
        "samples_per_regime": samples,
        "shells": shells_count,
        "balance_model": {
            "inequality": "nontrivial requires 1 <= 4*bias + drift",
            "bias": "weighted_mean(lambda(c)*(kappa^2-1/2)) / weighted_mean(lambda(c))",
            "drift": "normalized nonlinear sweeping proxy",
            "OU_lower_bound": "2*int|grad omega|^2 G - 1/2*int|omega|^2 G >= Omega_G",
        },
        "regimes": regimes,
        "checks": checks,
        "conclusion": (
            "Diagnostic only: neutral arcsine/NRS and stationary-proxy regimes "
            "fail the nontrivial balance requirement, while deliberately biased "
            "or drift-dominated counter-regimes can satisfy it. This supports "
            "AbelTriadicDefectMeasureConstruction and NSTypeIBlowupKappaBiasBound "
            "as the live PDE gaps, but proves neither."
        ),
        "promotion": {
            "finite_diagnostic": True,
            "pde_gate_closed": False,
            "clay": False,
            "reason": "proxy samples only; no Abel measure construction or PDE identity",
        },
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    payload = run(samples=args.samples, shells_count=args.shells, seed=args.seed)
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(payload, sort_keys=True))
    else:
        print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
