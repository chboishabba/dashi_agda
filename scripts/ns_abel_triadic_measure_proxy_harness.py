#!/usr/bin/env python3
"""Abel-weighted NS triadic defect-measure proxy.

This pure-stdlib harness samples the local angular S2 Biot-Savart eigenbundle
model and builds a finite Abel-weighted proxy for a propagated triadic measure.
For each sampled cascade path, depth d contributes weight

    (1 - rho) * rho^d.

The harness records kappa moments, lambda-weighted kappa bias, great-circle
coverage of output directions, and a one-step pushforward residual comparing
the Abel proxy to its transition image.  It is a diagnostic surface only: it is
not a PDE construction of an Abel defect measure and it does not promote Clay.
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

EPS = 1.0e-12
SCRIPT_DIR = Path(__file__).resolve().parent
PROVIDER_PATH = SCRIPT_DIR / "ns_s2_biot_savart_eigenbundle.py"


@dataclass(frozen=True)
class TriadState:
    depth: int
    shell: int
    a: Vec3
    b: Vec3
    c: Vec3
    omega_hat: Vec3
    kappa: float
    lambda_weight: float
    stretching_factor: float
    bias: float


@dataclass(frozen=True)
class WeightedMoments:
    count: int
    total_weight: float
    mean_kappa: float | None
    mean_abs_kappa: float | None
    mean_kappa_sq: float | None
    mean_kappa_fourth: float | None
    coherent_fraction_01: float | None
    coherent_fraction_sqrt_half: float | None
    mean_lambda: float | None
    mean_lambda_sq: float | None
    mean_bias: float | None
    mean_stretching: float | None


@dataclass(frozen=True)
class CoverageSummary:
    normals: int
    output_count: int
    max_great_circle_gap: float | None
    mean_great_circle_gap: float | None
    coverage_score: float | None


@dataclass(frozen=True)
class StationarityResidual:
    moment_l1_residual: float | None
    bin_l1_residual: float | None
    source_mean_bias: float | None
    pushed_mean_bias: float | None
    source_mean_kappa_sq: float | None
    pushed_mean_kappa_sq: float | None
    source_mean_lambda: float | None
    pushed_mean_lambda: float | None


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=6000, help="Number of cascade paths.")
    parser.add_argument("--depths", type=int, default=8, help="Number of depths per path.")
    parser.add_argument("--abel-rho", type=float, default=0.85, help="Abel rho in [0,1).")
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument("--coverage-normals", type=int, default=160)
    parser.add_argument("--bins", type=int, default=24, help="Bins for kappa stationarity residual.")
    parser.add_argument("--json-output", type=Path, default=None)
    parser.add_argument("--json", action="store_true")
    return parser.parse_args(argv)


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


def project_tangent(c: Vec3, v: Vec3) -> Vec3 | None:
    c_hat = normalize(c)
    if c_hat is None:
        return None
    return sub(v, scale(dot(v, c_hat), c_hat))


def random_unit(rng: random.Random) -> Vec3:
    z = rng.uniform(-1.0, 1.0)
    theta = rng.uniform(0.0, 2.0 * math.pi)
    r = math.sqrt(max(0.0, 1.0 - z * z))
    return (r * math.cos(theta), r * math.sin(theta), z)


def fibonacci_sphere(count: int) -> list[Vec3]:
    if count <= 0:
        raise ValueError("coverage normal count must be positive")
    points: list[Vec3] = []
    golden_angle = math.pi * (3.0 - math.sqrt(5.0))
    for k in range(count):
        z = 1.0 - 2.0 * (k + 0.5) / count
        r = math.sqrt(max(0.0, 1.0 - z * z))
        theta = golden_angle * k
        points.append((r * math.cos(theta), r * math.sin(theta), z))
    return points


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


def coerce_vec3(value: Any) -> Vec3 | None:
    if isinstance(value, (tuple, list)) and len(value) == 3:
        try:
            out = (float(value[0]), float(value[1]), float(value[2]))
        except (TypeError, ValueError):
            return None
        if all(math.isfinite(x) for x in out):
            return out
    return None


def angular_bundle(module: ModuleType, c: Vec3) -> Any | None:
    fn = getattr(module, "angular_eigenbundle", None)
    if not callable(fn):
        raise AttributeError("provider does not expose angular_eigenbundle")
    return fn(c)


def state_from_pair(module: ModuleType, a: Vec3, b: Vec3, depth: int) -> TriadState | None:
    c = normalize(add(a, b))
    if c is None:
        return None
    bundle = angular_bundle(module, c)
    if bundle is None:
        return None
    omega_hat = coerce_vec3(getattr(bundle, "omega_hat", None))
    if omega_hat is None:
        return None
    omega_hat = normalize(omega_hat)
    if omega_hat is None:
        return None
    projected_b = project_tangent(c, b)
    if projected_b is None:
        return None
    projected_b_hat = normalize(projected_b)
    if projected_b_hat is None:
        return None

    m11 = float(getattr(bundle, "m11"))
    m12 = float(getattr(bundle, "m12"))
    lambda_weight = math.sqrt(max(0.0, m11 * m11 + m12 * m12))
    kappa = max(-1.0, min(1.0, dot(projected_b_hat, omega_hat)))
    stretching_factor = lambda_weight * (2.0 * kappa * kappa - 1.0)
    bias = lambda_weight * (kappa * kappa - 0.5)
    return TriadState(
        depth=depth,
        shell=1 << min(depth, 30),
        a=normalize(a) or a,
        b=normalize(b) or b,
        c=c,
        omega_hat=omega_hat,
        kappa=kappa,
        lambda_weight=lambda_weight,
        stretching_factor=stretching_factor,
        bias=bias,
    )


def transition(module: ModuleType, rng: random.Random, state: TriadState, depth: int) -> TriadState | None:
    for _ in range(8):
        nxt = state_from_pair(module, state.c, random_unit(rng), depth)
        if nxt is not None:
            return nxt
    return None


def sample_cascades(module: ModuleType, rng: random.Random, samples: int, depths: int) -> tuple[list[TriadState], list[TriadState]]:
    states: list[TriadState] = []
    pushed: list[TriadState] = []
    attempts = 0
    max_attempts = max(samples * 5, 1000)
    while attempts < max_attempts and len(pushed) < samples * depths:
        attempts += 1
        current = state_from_pair(module, random_unit(rng), random_unit(rng), 0)
        if current is None:
            continue
        path: list[TriadState] = []
        push_path: list[TriadState] = []
        for depth in range(depths):
            if current is None:
                break
            path.append(current)
            nxt = transition(module, rng, current, depth + 1)
            if nxt is None:
                break
            push_path.append(nxt)
            current = nxt
        if len(path) == depths and len(push_path) == depths:
            states.extend(path)
            pushed.extend(push_path)
    return states, pushed


def abel_weight(depth: int, rho: float) -> float:
    return (1.0 - rho) * (rho ** depth)


def weighted_mean(values: Iterable[tuple[float, float]]) -> float | None:
    total_weight = 0.0
    total = 0.0
    for value, weight in values:
        total += value * weight
        total_weight += weight
    if total_weight <= EPS:
        return None
    return total / total_weight


def moments(states: Sequence[TriadState], rho: float) -> WeightedMoments:
    weighted = [(s, abel_weight(s.depth, rho)) for s in states]
    total_weight = sum(w for _, w in weighted)
    if not states or total_weight <= EPS:
        return WeightedMoments(
            count=len(states),
            total_weight=total_weight,
            mean_kappa=None,
            mean_abs_kappa=None,
            mean_kappa_sq=None,
            mean_kappa_fourth=None,
            coherent_fraction_01=None,
            coherent_fraction_sqrt_half=None,
            mean_lambda=None,
            mean_lambda_sq=None,
            mean_bias=None,
            mean_stretching=None,
        )
    sqrt_half = 1.0 / math.sqrt(2.0)
    return WeightedMoments(
        count=len(states),
        total_weight=total_weight,
        mean_kappa=weighted_mean((s.kappa, w) for s, w in weighted),
        mean_abs_kappa=weighted_mean((abs(s.kappa), w) for s, w in weighted),
        mean_kappa_sq=weighted_mean((s.kappa * s.kappa, w) for s, w in weighted),
        mean_kappa_fourth=weighted_mean((s.kappa ** 4, w) for s, w in weighted),
        coherent_fraction_01=weighted_mean((1.0 if abs(s.kappa) < 0.1 else 0.0, w) for s, w in weighted),
        coherent_fraction_sqrt_half=weighted_mean((1.0 if abs(s.kappa) < sqrt_half else 0.0, w) for s, w in weighted),
        mean_lambda=weighted_mean((s.lambda_weight, w) for s, w in weighted),
        mean_lambda_sq=weighted_mean((s.lambda_weight * s.lambda_weight, w) for s, w in weighted),
        mean_bias=weighted_mean((s.bias, w) for s, w in weighted),
        mean_stretching=weighted_mean((s.stretching_factor, w) for s, w in weighted),
    )


def coverage(states: Sequence[TriadState], normal_count: int) -> CoverageSummary:
    if not states:
        return CoverageSummary(normal_count, 0, None, None, None)
    normals = fibonacci_sphere(normal_count)
    gaps: list[float] = []
    outputs = [s.c for s in states]
    for normal in normals:
        gaps.append(min(abs(dot(output, normal)) for output in outputs))
    max_gap = max(gaps) if gaps else None
    mean_gap = statistics.fmean(gaps) if gaps else None
    coverage_score = None if max_gap is None else max(0.0, 1.0 - max_gap)
    return CoverageSummary(
        normals=normal_count,
        output_count=len(outputs),
        max_great_circle_gap=max_gap,
        mean_great_circle_gap=mean_gap,
        coverage_score=coverage_score,
    )


def kappa_histogram(states: Sequence[TriadState], rho: float, bins: int) -> list[float]:
    hist = [0.0 for _ in range(bins)]
    for state in states:
        idx = int((max(-1.0, min(1.0, state.kappa)) + 1.0) * 0.5 * bins)
        idx = max(0, min(bins - 1, idx))
        hist[idx] += abel_weight(state.depth, rho)
    total = sum(hist)
    if total <= EPS:
        return hist
    return [x / total for x in hist]


def stationarity_residual(source: Sequence[TriadState], pushed: Sequence[TriadState], rho: float, bins: int) -> StationarityResidual:
    src = moments(source, rho)
    dst = moments(pushed, rho)
    moment_pairs = [
        (src.mean_kappa_sq, dst.mean_kappa_sq),
        (src.mean_lambda, dst.mean_lambda),
        (src.mean_bias, dst.mean_bias),
        (src.mean_stretching, dst.mean_stretching),
    ]
    diffs = [abs(a - b) for a, b in moment_pairs if a is not None and b is not None]
    moment_l1 = sum(diffs) if diffs else None

    src_hist = kappa_histogram(source, rho, bins)
    dst_hist = kappa_histogram(pushed, rho, bins)
    bin_l1 = sum(abs(a - b) for a, b in zip(src_hist, dst_hist))

    return StationarityResidual(
        moment_l1_residual=moment_l1,
        bin_l1_residual=bin_l1,
        source_mean_bias=src.mean_bias,
        pushed_mean_bias=dst.mean_bias,
        source_mean_kappa_sq=src.mean_kappa_sq,
        pushed_mean_kappa_sq=dst.mean_kappa_sq,
        source_mean_lambda=src.mean_lambda,
        pushed_mean_lambda=dst.mean_lambda,
    )


def validate_args(args: argparse.Namespace) -> None:
    if args.samples <= 0:
        raise ValueError("--samples must be positive")
    if args.depths <= 0:
        raise ValueError("--depths must be positive")
    if not (0.0 <= args.abel_rho < 1.0):
        raise ValueError("--abel-rho must satisfy 0 <= rho < 1")
    if args.coverage_normals <= 0:
        raise ValueError("--coverage-normals must be positive")
    if args.bins <= 1:
        raise ValueError("--bins must be greater than 1")


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    validate_args(args)
    rng = random.Random(args.seed)
    module = load_provider()
    states, pushed = sample_cascades(module, rng, args.samples, args.depths)
    source_moments = moments(states, args.abel_rho)
    pushed_moments = moments(pushed, args.abel_rho)
    result = {
        "ok": bool(states and pushed),
        "samples": args.samples,
        "depths": args.depths,
        "abel_rho": args.abel_rho,
        "seed": args.seed,
        "accepted_states": len(states),
        "accepted_pushforward_states": len(pushed),
        "source": asdict(source_moments),
        "pushforward": asdict(pushed_moments),
        "angular_coverage": asdict(coverage(states, args.coverage_normals)),
        "pushforward_angular_coverage": asdict(coverage(pushed, args.coverage_normals)),
        "stationarity_residual": asdict(stationarity_residual(states, pushed, args.abel_rho, args.bins)),
        "arcsine_reference": {
            "mean_kappa_sq": 0.5,
            "mean_kappa_fourth": 0.375,
            "coherent_fraction_01": 2.0 * math.asin(0.1) / math.pi,
            "negative_stretching_fraction_threshold": 0.5,
        },
        "finite_measure_proxy": True,
        "abel_defect_measure_constructed": False,
        "pde_promotion": False,
        "clay_promotion": False,
    }
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(result, sort_keys=True))
    else:
        print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
