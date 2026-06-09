#!/usr/bin/env python3
"""Approximate NS kappa-bias variational diagnostic.

This pure-stdlib harness samples the local S2 Biot-Savart eigenbundle model
and estimates how much positive weighted kappa bias can be selected under
three finite proxy regimes:

* unconstrained top-tail: maximize lambda(c) * (kappa^2 - 1/2) directly;
* stationarity proxy: select top-tail states, push them through one random
  one-step continuation, and re-score the transported states;
* Lei-Ren-Tian proxy: greedily select high-bias states while improving a
  great-circle hitting proxy over sampled normal directions.

The output is a falsification/diagnostic surface only.  It is not a PDE proof,
not a Type-I blowup theorem, and not a Clay promotion receipt.
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

EPS = 1.0e-12
SCRIPT_DIR = Path(__file__).resolve().parent
PROVIDER_PATH = SCRIPT_DIR / "ns_s2_biot_savart_eigenbundle.py"


@dataclass(frozen=True)
class State:
    a: Vec3
    b: Vec3
    c: Vec3
    omega_hat: Vec3
    lambda_weight: float
    kappa: float
    bias: float


@dataclass(frozen=True)
class SelectionSummary:
    selected_count: int
    mean_bias: float | None
    mean_lambda: float | None
    mean_kappa_sq: float | None
    coverage_score: float | None
    max_great_circle_gap: float | None


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=12000)
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument("--top-fraction", type=float, default=0.05)
    parser.add_argument("--coverage-normals", type=int, default=192)
    parser.add_argument(
        "--lrt-candidate-multiplier",
        type=float,
        default=8.0,
        help="Number of top candidates considered for greedy LRT proxy, as a multiple of selected count.",
    )
    parser.add_argument(
        "--json-output",
        type=Path,
        default=None,
        help="Optional path for a deterministic JSON receipt.",
    )
    parser.add_argument("--json", action="store_true", help="Emit JSON only.")
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
        raise ValueError("sphere sample count must be positive")
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
    try:
        return fn(c)
    except TypeError:
        return None


def state_from_pair(module: ModuleType, a: Vec3, b: Vec3) -> State | None:
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

    m11 = float(getattr(bundle, "m11"))
    m12 = float(getattr(bundle, "m12"))
    lambda_weight = math.sqrt(max(0.0, m11 * m11 + m12 * m12))

    projected_b = project_tangent(c, b)
    if projected_b is None:
        return None
    projected_b_hat = normalize(projected_b)
    if projected_b_hat is None:
        return None

    kappa = max(-1.0, min(1.0, dot(projected_b_hat, omega_hat)))
    bias = lambda_weight * (kappa * kappa - 0.5)
    return State(
        a=normalize(a) or a,
        b=normalize(b) or b,
        c=c,
        omega_hat=omega_hat,
        lambda_weight=lambda_weight,
        kappa=kappa,
        bias=bias,
    )


def sample_states(module: ModuleType, rng: random.Random, count: int) -> list[State]:
    states: list[State] = []
    attempts = 0
    max_attempts = max(1000, count * 4)
    while len(states) < count and attempts < max_attempts:
        attempts += 1
        state = state_from_pair(module, random_unit(rng), random_unit(rng))
        if state is not None:
            states.append(state)
    return states


def selected_count(total: int, top_fraction: float) -> int:
    if total <= 0:
        return 0
    if not (0.0 < top_fraction <= 1.0):
        raise ValueError("--top-fraction must be in (0, 1]")
    return max(1, min(total, int(round(total * top_fraction))))


def summarize_selection(states: Sequence[State], normals: Sequence[Vec3]) -> SelectionSummary:
    if not states:
        return SelectionSummary(
            selected_count=0,
            mean_bias=None,
            mean_lambda=None,
            mean_kappa_sq=None,
            coverage_score=None,
            max_great_circle_gap=None,
        )

    gaps = [min(abs(dot(normal, state.c)) for state in states) for normal in normals]
    # A perfect LRT proxy hit has min |n.c| = 0 for every sampled normal.
    # Clamp to [0,1] because finite samples can only approximate coverage.
    mean_gap = statistics.fmean(gaps) if gaps else 1.0
    max_gap = max(gaps) if gaps else 1.0
    coverage = max(0.0, min(1.0, 1.0 - mean_gap))
    return SelectionSummary(
        selected_count=len(states),
        mean_bias=statistics.fmean(state.bias for state in states),
        mean_lambda=statistics.fmean(state.lambda_weight for state in states),
        mean_kappa_sq=statistics.fmean(state.kappa * state.kappa for state in states),
        coverage_score=coverage,
        max_great_circle_gap=max_gap,
    )


def top_tail(states: Sequence[State], count: int) -> list[State]:
    return sorted(states, key=lambda item: item.bias, reverse=True)[:count]


def stationary_proxy(module: ModuleType, rng: random.Random, selected: Sequence[State]) -> list[State]:
    transported: list[State] = []
    for state in selected:
        # One-step transition proxy: carry the output direction forward as the
        # first input and resample the interacting mode.
        next_state = state_from_pair(module, state.c, random_unit(rng))
        if next_state is not None:
            transported.append(next_state)
    return transported


def greedy_lrt_proxy(states: Sequence[State], count: int, normals: Sequence[Vec3], candidate_multiplier: float) -> list[State]:
    if count <= 0 or not states:
        return []
    candidate_count = max(count, min(len(states), int(round(count * max(1.0, candidate_multiplier)))))
    candidates = top_tail(states, candidate_count)
    selected = candidates[: min(count, len(candidates))]
    if not selected or not normals:
        return selected

    selected_ids = {id(state) for state in selected}
    reserve = [state for state in candidates if id(state) not in selected_ids]
    if not reserve:
        return selected

    # Fast coverage pass: keep the high-bias top-tail as the base measure,
    # then replace a small number of low-bias selected states with reserve
    # states that hit the currently worst sampled great-circle normal.  This is
    # an approximate LRT proxy, not an exact combinatorial optimizer.
    max_rounds = min(len(reserve), max(8, min(96, count // 3)))
    gaps = [min(abs(dot(normal, state.c)) for state in selected) for normal in normals]
    for _ in range(max_rounds):
        worst_index, worst_gap = max(enumerate(gaps), key=lambda item: item[1])
        if worst_gap <= 0.01:
            break
        worst_normal = normals[worst_index]
        best_state: State | None = None
        best_hit = worst_gap
        for state in reserve:
            hit = abs(dot(worst_normal, state.c))
            if hit < best_hit:
                best_state = state
                best_hit = hit
        if best_state is None:
            break

        replacement_index, replacement = min(enumerate(selected), key=lambda item: item[1].bias)
        if best_state.bias < replacement.bias and (worst_gap - best_hit) < 0.02:
            break
        selected[replacement_index] = best_state
        reserve.remove(best_state)
        gaps = [min(old, abs(dot(normal, best_state.c))) for old, normal in zip(gaps, normals)]
    return selected


def quantiles(values: Sequence[float]) -> dict[str, float | None]:
    finite = sorted(x for x in values if math.isfinite(x))
    if not finite:
        return {"count": 0, "min": None, "p05": None, "median": None, "mean": None, "p95": None, "max": None}

    def pct(q: float) -> float:
        index = min(len(finite) - 1, max(0, int(round(q * (len(finite) - 1)))))
        return finite[index]

    return {
        "count": len(finite),
        "min": finite[0],
        "p05": pct(0.05),
        "median": statistics.median(finite),
        "mean": statistics.fmean(finite),
        "p95": pct(0.95),
        "max": finite[-1],
    }


def run(args: argparse.Namespace) -> dict[str, Any]:
    if args.samples <= 0:
        raise ValueError("--samples must be positive")
    if args.coverage_normals <= 0:
        raise ValueError("--coverage-normals must be positive")

    rng = random.Random(args.seed)
    provider = load_provider()
    states = sample_states(provider, rng, args.samples)
    count = selected_count(len(states), args.top_fraction)
    normals = fibonacci_sphere(args.coverage_normals)

    unconstrained = top_tail(states, count)
    stationary = stationary_proxy(provider, rng, unconstrained)
    lrt = greedy_lrt_proxy(states, count, normals, args.lrt_candidate_multiplier)
    lrt_and_stationary = stationary_proxy(provider, rng, lrt)

    all_summary = summarize_selection(states, normals)
    unconstrained_summary = summarize_selection(unconstrained, normals)
    stationary_summary = summarize_selection(stationary, normals)
    lrt_summary = summarize_selection(lrt, normals)
    lrt_stationary_summary = summarize_selection(lrt_and_stationary, normals)

    active_constraints = {
        "unconstrained": [],
        "LRT_constrained": [
            "sampled_great_circle_hitting_proxy",
            "greedy_high_bias_coverage_replacement",
        ],
        "stationary_proxy": [
            "one_step_true_leray_direction_transport_proxy",
            "resampled_interacting_mode",
        ],
        "LRT_and_stationary_proxy": [
            "sampled_great_circle_hitting_proxy",
            "greedy_high_bias_coverage_replacement",
            "one_step_true_leray_direction_transport_proxy",
            "resampled_interacting_mode",
        ],
    }

    conclusion = (
        "NSTypeIBlowupKappaBiasBound remains open: this finite S2 proxy can "
        "select positive kappa-bias under top-tail/LRT proxies, while the "
        "one-step stationarity proxy may reduce or erase it. No Type-I "
        "self-similar PDE measure, Abel triadic defect construction, or "
        "residual depletion theorem is proved."
    )

    return {
        "harness": "ns_kappa_bias_variational_harness",
        "scope": "finite_s2_variational_proxy_not_pde_proof",
        "provider": str(PROVIDER_PATH),
        "seed": args.seed,
        "requested_samples": args.samples,
        "accepted_samples": len(states),
        "top_fraction": args.top_fraction,
        "target_selected_count": count,
        "coverage_normals": args.coverage_normals,
        "bias_definition": "lambda_weight*(kappa^2-1/2)",
        "lambda_weight_definition": "sqrt(m11^2+m12^2) from ns_s2_biot_savart_eigenbundle.angular_eigenbundle",
        "kappa_definition": "dot(normalize(P_c b), omega_hat(c))",
        "max_bias_unconstrained": unconstrained_summary.mean_bias,
        "max_bias_LRT_constrained": lrt_summary.mean_bias,
        "max_bias_stationary_proxy": stationary_summary.mean_bias,
        "max_bias_LRT_and_stationary_proxy": lrt_stationary_summary.mean_bias,
        "active_constraints": active_constraints,
        "conclusion": conclusion,
        "baseline_all_mean_bias": all_summary.mean_bias,
        "unconstrained_max_mean_bias": unconstrained_summary.mean_bias,
        "stationary_proxy_mean_bias": stationary_summary.mean_bias,
        "lrt_proxy_mean_bias": lrt_summary.mean_bias,
        "lrt_and_stationary_proxy_mean_bias": lrt_stationary_summary.mean_bias,
        "coverage_score": lrt_summary.coverage_score,
        "unconstrained_coverage_score": unconstrained_summary.coverage_score,
        "stationary_proxy_coverage_score": stationary_summary.coverage_score,
        "lrt_and_stationary_proxy_coverage_score": lrt_stationary_summary.coverage_score,
        "selected_counts": {
            "unconstrained": unconstrained_summary.selected_count,
            "stationary_proxy": stationary_summary.selected_count,
            "lrt_proxy": lrt_summary.selected_count,
            "lrt_and_stationary_proxy": lrt_stationary_summary.selected_count,
        },
        "max_great_circle_gaps": {
            "unconstrained": unconstrained_summary.max_great_circle_gap,
            "stationary_proxy": stationary_summary.max_great_circle_gap,
            "lrt_proxy": lrt_summary.max_great_circle_gap,
            "lrt_and_stationary_proxy": lrt_stationary_summary.max_great_circle_gap,
        },
        "summaries": {
            "all": asdict(all_summary),
            "unconstrained": asdict(unconstrained_summary),
            "stationary_proxy": asdict(stationary_summary),
            "lrt_proxy": asdict(lrt_summary),
            "lrt_and_stationary_proxy": asdict(lrt_stationary_summary),
        },
        "quantiles": {
            "bias": quantiles([state.bias for state in states]),
            "kappa_abs": quantiles([abs(state.kappa) for state in states]),
            "kappa_sq": quantiles([state.kappa * state.kappa for state in states]),
            "lambda_weight": quantiles([state.lambda_weight for state in states]),
        },
        "promotion": {
            "clay": False,
            "pde_gate_closed": False,
            "reason": "finite proxy only; Type-I/self-similar kappa-bias bound remains open",
        },
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    result = run(args)
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(result, sort_keys=True))
    else:
        print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
