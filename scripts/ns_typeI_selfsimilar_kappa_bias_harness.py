#!/usr/bin/env python3
"""Type-I/self-similar kappa-bias proxy diagnostic.

This pure-stdlib harness probes the current NS PDE gate:

    can a Type-I/self-similar profile create persistent positive
    lambda(c) * (kappa^2 - 1/2) bias after diffusion/drift penalties?

It is deliberately a proxy.  It samples synthetic shell profiles, uses the
local S2 Biot-Savart/curl eigenbundle provider for the angular strain
lambda(c), and applies a finite stationary-balance surrogate:

* diffusion weight: |xi|^2 on each shell;
* drift weight: 0.5 * d log(amplitude) / d log(|xi|);
* pressure/triadic transfer proxy: lambda(c) * (kappa^2 - 1/2).

The result is a falsification/diagnostic surface only.  It is not a Type-I
blowup theorem, not an Abel-triadic measure construction, and not Clay
promotion.
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
from typing import Any, Iterable, Sequence


Vec3 = tuple[float, float, float]

SCRIPT_DIR = Path(__file__).resolve().parent
PROVIDER_PATH = SCRIPT_DIR / "ns_s2_biot_savart_eigenbundle.py"
EPS = 1.0e-12
PROFILE_NAMES = ("neutral", "forward_bias", "depleted")


@dataclass(frozen=True)
class Shell:
    index: int
    radius: float
    amplitude: float
    slope: float
    normalized_diffusion: float
    drift_weight: float


@dataclass(frozen=True)
class Sample:
    profile: str
    shell_index: int
    radius: float
    amplitude_sq: float
    lambda_weight: float
    kappa: float
    raw_bias: float
    weighted_bias: float
    diffusion_penalty: float
    drift_penalty: float
    total_penalty: float
    net_bias: float


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=12000)
    parser.add_argument("--shells", type=int, default=12)
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument(
        "--profile",
        choices=PROFILE_NAMES + ("all",),
        default="all",
        help="Synthetic profile family to sample.",
    )
    parser.add_argument(
        "--penalty-scale",
        type=float,
        default=0.08,
        help="Scale applied to the diffusion/drift stationary-balance penalty.",
    )
    parser.add_argument("--json-output", type=Path, default=None)
    parser.add_argument("--json", action="store_true")
    return parser.parse_args(argv)


def add(u: Vec3, v: Vec3) -> Vec3:
    return (u[0] + v[0], u[1] + v[1], u[2] + v[2])


def scale(s: float, u: Vec3) -> Vec3:
    return (s * u[0], s * u[1], s * u[2])


def dot(u: Vec3, v: Vec3) -> float:
    return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]


def norm(u: Vec3) -> float:
    return math.sqrt(max(0.0, dot(u, u)))


def normalize(u: Vec3, eps: float = EPS) -> Vec3 | None:
    n = norm(u)
    if n <= eps:
        return None
    return scale(1.0 / n, u)


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


def random_unit(rng: random.Random) -> Vec3:
    z = rng.uniform(-1.0, 1.0)
    theta = rng.uniform(0.0, 2.0 * math.pi)
    r = math.sqrt(max(0.0, 1.0 - z * z))
    return (r * math.cos(theta), r * math.sin(theta), z)


def coerce_vec3(value: Any) -> Vec3 | None:
    if not isinstance(value, (tuple, list)) or len(value) != 3:
        return None
    try:
        out = (float(value[0]), float(value[1]), float(value[2]))
    except (TypeError, ValueError):
        return None
    if not all(math.isfinite(x) for x in out):
        return None
    return out


def profile_amplitude(profile: str, radius: float) -> float:
    log_r = math.log(radius)
    if profile == "neutral":
        return math.exp(-0.34 * log_r * log_r)
    if profile == "forward_bias":
        return math.exp(-0.18 * (log_r - 0.35) * (log_r - 0.35))
    if profile == "depleted":
        return math.exp(-0.28 * (log_r + 0.25) * (log_r + 0.25)) / math.sqrt(1.0 + 0.18 * radius * radius)
    raise ValueError(f"unknown profile: {profile}")


def build_shells(profile: str, count: int) -> list[Shell]:
    if count < 3:
        raise ValueError("--shells must be at least 3")
    log_min = math.log(0.35)
    log_max = math.log(2.6)
    logs = [log_min + (log_max - log_min) * k / (count - 1) for k in range(count)]
    radii = [math.exp(x) for x in logs]
    amps = [profile_amplitude(profile, r) for r in radii]
    slopes: list[float] = []
    for idx in range(count):
        if idx == 0:
            slope = (math.log(amps[1]) - math.log(amps[0])) / (logs[1] - logs[0])
        elif idx == count - 1:
            slope = (math.log(amps[-1]) - math.log(amps[-2])) / (logs[-1] - logs[-2])
        else:
            slope = (math.log(amps[idx + 1]) - math.log(amps[idx - 1])) / (logs[idx + 1] - logs[idx - 1])
        slopes.append(slope)

    max_r_sq = max(r * r for r in radii)
    return [
        Shell(
            index=idx,
            radius=r,
            amplitude=amps[idx],
            slope=slopes[idx],
            normalized_diffusion=(r * r) / max_r_sq,
            drift_weight=0.5 * slopes[idx],
        )
        for idx, r in enumerate(radii)
    ]


def shell_choice(rng: random.Random, shells: Sequence[Shell]) -> Shell:
    weights = [shell.amplitude * shell.amplitude for shell in shells]
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


def sample_kappa(profile: str, shell: Shell, rng: random.Random) -> float:
    theta = rng.uniform(0.0, 2.0 * math.pi)
    if profile == "neutral":
        return math.cos(theta)

    sign = -1.0 if rng.random() < 0.5 else 1.0

    if profile == "forward_bias":
        # Bias toward |kappa| > 1/sqrt(2), stronger on the upper shells.
        u = rng.random()
        high = math.sqrt(0.5 + 0.5 * (1.0 - u * u))
        return sign * min(1.0, high)

    if profile == "depleted":
        # Bias toward compressive / low-kappa states.
        u = rng.random()
        low = math.sqrt(0.5) * u * u
        return sign * min(1.0, low)

    raise ValueError(f"unknown profile: {profile}")


def lambda_from_direction(provider: ModuleType, c: Vec3) -> tuple[float, Vec3, Vec3] | None:
    bundle = provider.angular_eigenbundle(c, EPS)
    if bundle is None:
        return None
    e_plus = coerce_vec3(getattr(bundle, "e_plus", None))
    omega_hat = coerce_vec3(getattr(bundle, "omega_hat", None))
    if e_plus is None or omega_hat is None:
        return None
    m11 = float(getattr(bundle, "m11"))
    m12 = float(getattr(bundle, "m12"))
    return math.hypot(m11, m12), e_plus, omega_hat


def sample_one(provider: ModuleType, profile: str, shell: Shell, rng: random.Random, penalty_scale: float) -> Sample | None:
    c = random_unit(rng)
    angular = lambda_from_direction(provider, c)
    if angular is None:
        return None
    lambda_weight, e_plus, omega_hat = angular
    kappa = sample_kappa(profile, shell, rng)

    # Reconstruct a tangent output direction so the sample is anchored to the
    # same finite-symbol geometry as the stretching-formula harness.
    tangent = add(scale(math.sqrt(max(0.0, 1.0 - kappa * kappa)), e_plus), scale(kappa, omega_hat))
    if normalize(tangent) is None:
        return None

    amplitude_sq = shell.amplitude * shell.amplitude
    raw_bias = lambda_weight * (kappa * kappa - 0.5)
    weighted_bias = amplitude_sq * raw_bias
    diffusion_penalty = amplitude_sq * shell.normalized_diffusion
    drift_penalty = amplitude_sq * abs(shell.drift_weight)
    total_penalty = penalty_scale * (diffusion_penalty + drift_penalty)
    net_bias = weighted_bias - total_penalty
    return Sample(
        profile=profile,
        shell_index=shell.index,
        radius=shell.radius,
        amplitude_sq=amplitude_sq,
        lambda_weight=lambda_weight,
        kappa=kappa,
        raw_bias=raw_bias,
        weighted_bias=weighted_bias,
        diffusion_penalty=diffusion_penalty,
        drift_penalty=drift_penalty,
        total_penalty=total_penalty,
        net_bias=net_bias,
    )


def quantile(values: Sequence[float], q: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    idx = min(len(ordered) - 1, max(0, int(round(q * (len(ordered) - 1)))))
    return ordered[idx]


def summarize(profile: str, samples: Sequence[Sample], shells: Sequence[Shell]) -> dict[str, object]:
    if not samples:
        return {
            "profile": profile,
            "accepted_samples": 0,
            "error": "no_samples",
            "pde_promotion": False,
            "clay_promotion": False,
        }

    raw = [x.raw_bias for x in samples]
    weighted = [x.weighted_bias for x in samples]
    penalties = [x.total_penalty for x in samples]
    net = [x.net_bias for x in samples]
    kappa_sq = [x.kappa * x.kappa for x in samples]
    positive_net = [x for x in samples if x.net_bias > 0.0]
    positive_weighted = [x for x in samples if x.weighted_bias > 0.0]
    shell_rows = []
    for shell in shells:
        members = [x for x in samples if x.shell_index == shell.index]
        if not members:
            continue
        shell_rows.append(
            {
                "index": shell.index,
                "radius": shell.radius,
                "amplitude": shell.amplitude,
                "slope": shell.slope,
                "normalized_diffusion": shell.normalized_diffusion,
                "drift_weight": shell.drift_weight,
                "count": len(members),
                "mean_net_bias": statistics.fmean(x.net_bias for x in members),
                "mean_weighted_bias": statistics.fmean(x.weighted_bias for x in members),
                "positive_net_fraction": sum(1 for x in members if x.net_bias > 0.0) / len(members),
            }
        )

    return {
        "profile": profile,
        "accepted_samples": len(samples),
        "mean_kappa_sq": statistics.fmean(kappa_sq),
        "mean_lambda": statistics.fmean(x.lambda_weight for x in samples),
        "mean_raw_bias": statistics.fmean(raw),
        "mean_weighted_bias": statistics.fmean(weighted),
        "mean_penalty": statistics.fmean(penalties),
        "mean_net_bias_after_penalty": statistics.fmean(net),
        "positive_weighted_bias_fraction": len(positive_weighted) / len(samples),
        "positive_net_bias_fraction": len(positive_net) / len(samples),
        "max_net_bias": max(net),
        "net_bias_q50": quantile(net, 0.5),
        "net_bias_q90": quantile(net, 0.9),
        "net_bias_q99": quantile(net, 0.99),
        "creates_positive_mean_after_penalty": statistics.fmean(net) > 0.0,
        "creates_any_positive_after_penalty": bool(positive_net),
        "shell_summaries": shell_rows,
        "pde_promotion": False,
        "clay_promotion": False,
    }


def run_profile(provider: ModuleType, profile: str, samples: int, shells_count: int, seed: int, penalty_scale: float) -> dict[str, object]:
    rng = random.Random(seed)
    shells = build_shells(profile, shells_count)
    rows: list[Sample] = []
    attempts = 0
    max_attempts = max(samples * 4, samples + 100)
    while len(rows) < samples and attempts < max_attempts:
        attempts += 1
        shell = shell_choice(rng, shells)
        row = sample_one(provider, profile, shell, rng, penalty_scale)
        if row is not None:
            rows.append(row)
    if len(rows) < samples:
        raise RuntimeError(f"{profile}: accepted only {len(rows)}/{samples} samples")
    result = summarize(profile, rows, shells)
    result["attempts"] = attempts
    return result


def run(samples: int, shells: int, seed: int, profile: str, penalty_scale: float) -> dict[str, object]:
    if samples <= 0:
        raise ValueError("--samples must be positive")
    provider = load_provider()
    profiles = list(PROFILE_NAMES) if profile == "all" else [profile]
    per_profile = {
        name: run_profile(provider, name, samples, shells, seed + 7919 * idx, penalty_scale)
        for idx, name in enumerate(profiles)
    }
    positive_mean_profiles = [
        name for name, row in per_profile.items()
        if bool(row.get("creates_positive_mean_after_penalty"))
    ]
    return {
        "ok": True,
        "harness": "ns_typeI_selfsimilar_kappa_bias_harness",
        "scope": "synthetic_typeI_stationary_balance_proxy_not_pde_proof",
        "samples_per_profile": samples,
        "shells": shells,
        "seed": seed,
        "profile": profile,
        "penalty_scale": penalty_scale,
        "profiles": per_profile,
        "positive_mean_profiles_after_penalty": positive_mean_profiles,
        "any_profile_positive_mean_after_penalty": bool(positive_mean_profiles),
        "interpretation": (
            "positive proxy bias marks a PDE target requiring real Type-I/Abel measure control; "
            "negative proxy bias does not prove NS regularity"
        ),
        "pde_promotion": False,
        "clay_promotion": False,
    }


def emit(payload: dict[str, object], args: argparse.Namespace) -> None:
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(payload, sort_keys=True))
    else:
        print(json.dumps(payload, indent=2, sort_keys=True))


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    payload = run(
        samples=args.samples,
        shells=args.shells,
        seed=args.seed,
        profile=args.profile,
        penalty_scale=args.penalty_scale,
    )
    emit(payload, args)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
