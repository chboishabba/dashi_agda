"""Exact finite carrier primitives for the NS canonical Gamma-gap audit."""

from __future__ import annotations

from dataclasses import dataclass
import itertools
import math
from typing import Any, Sequence

import numpy as np


@dataclass(frozen=True)
class Mode:
    wavevector: tuple[int, int, int]
    dissipation_weight: float


@dataclass(frozen=True)
class Triad:
    left: int
    right: int
    out: int
    coefficient: float
    orbit_id: str | None = None


@dataclass(frozen=True)
class Problem:
    problem_id: str
    viscosity: float
    modes: tuple[Mode, ...]
    triads: tuple[Triad, ...]
    convention: str = "left_plus_right_equals_out"
    coefficient_semantics: str = "explicit_signed_transfer_coefficient"
    profiles: tuple[dict[str, Any], ...] = ()


@dataclass(frozen=True)
class Constraints:
    max_neff: float | None = None
    max_radial_variance: float | None = None
    min_peak_mass: float | None = None
    max_dissipation: float | None = None


@dataclass(frozen=True)
class SearchConfig:
    target_eta: float
    random_samples: int
    local_steps: int
    seeds: tuple[int, ...]
    zero_eps: float
    constraints: Constraints
    cancellation_cap: float
    envelope_cap: float
    window_sizes: tuple[int, ...]


def finite(value: Any, name: str) -> float:
    try:
        result = float(value)
    except (TypeError, ValueError) as exc:
        raise ValueError(f"{name} must be a finite number") from exc
    if not math.isfinite(result):
        raise ValueError(f"{name} must be finite")
    return result


def parse_wavevector(value: Any, name: str) -> tuple[int, int, int]:
    if not isinstance(value, (list, tuple)) or len(value) != 3:
        raise ValueError(f"{name} must be a length-3 integer vector")
    out: list[int] = []
    for coordinate in value:
        if isinstance(coordinate, bool):
            raise ValueError(f"{name} must contain integers")
        parsed = int(coordinate)
        if float(coordinate) != float(parsed):
            raise ValueError(f"{name} must contain integers")
        out.append(parsed)
    return out[0], out[1], out[2]


def normalize_probability(values: Sequence[float], zero_eps: float) -> np.ndarray:
    p = np.asarray(values, dtype=np.float64)
    if p.ndim != 1 or p.size == 0:
        raise ValueError("probability must be a nonempty one-dimensional vector")
    if not np.all(np.isfinite(p)):
        raise ValueError("probability contains a non-finite value")
    if np.any(p < -float(zero_eps)):
        raise ValueError("probability contains a negative value")
    p = np.maximum(p, 0.0)
    total = float(np.sum(p))
    if total <= float(zero_eps):
        raise ValueError("probability has zero total mass")
    return p / total


def zero_sum_vectors(problem: Problem, triad: Triad) -> tuple[tuple[int, int, int], ...]:
    left = problem.modes[triad.left].wavevector
    right = problem.modes[triad.right].wavevector
    out = problem.modes[triad.out].wavevector
    if problem.convention == "left_plus_right_equals_out":
        return left, right, tuple(-x for x in out)
    if problem.convention == "zero_sum":
        return left, right, out
    raise ValueError(f"unsupported triad convention: {problem.convention}")


def canonical_orbit_key(problem: Problem, triad: Triad) -> str:
    """Canonicalize under S3 permutations and simultaneous sign reversal."""

    if triad.orbit_id is not None:
        return f"explicit:{triad.orbit_id}"
    vectors = zero_sum_vectors(problem, triad)
    candidates: list[tuple[tuple[int, int, int], ...]] = []
    for permutation in itertools.permutations(vectors):
        candidates.append(tuple(permutation))
        candidates.append(
            tuple(tuple(-coordinate for coordinate in vector) for vector in permutation)
        )
    canonical = min(candidates)
    return "orbit:" + ";".join(
        ",".join(str(x) for x in vector) for vector in canonical
    )


def validate_problem(problem: Problem, zero_eps: float = 1.0e-12) -> None:
    if not problem.problem_id:
        raise ValueError("problem_id must be nonempty")
    if not math.isfinite(problem.viscosity) or problem.viscosity <= 0.0:
        raise ValueError("viscosity must be positive and finite")
    if not problem.modes:
        raise ValueError("problem must contain at least one mode")
    for index, mode in enumerate(problem.modes):
        if not math.isfinite(mode.dissipation_weight) or mode.dissipation_weight < 0.0:
            raise ValueError(f"mode {index} has invalid dissipation_weight")
    for index, triad in enumerate(problem.triads):
        for field_name, mode_index in (
            ("left", triad.left),
            ("right", triad.right),
            ("out", triad.out),
        ):
            if mode_index < 0 or mode_index >= len(problem.modes):
                raise ValueError(f"triad {index} {field_name} index is out of range")
        if len({triad.left, triad.right, triad.out}) < 3:
            raise ValueError(f"triad {index} must contain three distinct mode indices")
        if not math.isfinite(triad.coefficient):
            raise ValueError(f"triad {index} coefficient is not finite")
        zero_sum = np.sum(
            np.asarray(zero_sum_vectors(problem, triad), dtype=np.int64), axis=0
        )
        if np.any(zero_sum != 0):
            raise ValueError(
                f"triad {index} does not satisfy the declared zero-sum convention"
            )
    for profile in problem.profiles:
        probability = profile.get("probability")
        if not isinstance(probability, list) or len(probability) != len(problem.modes):
            raise ValueError("every profile probability must match the mode count")
        normalize_probability(probability, zero_eps)


def profile_metrics(
    problem: Problem, probability: Sequence[float], zero_eps: float
) -> dict[str, Any]:
    p = normalize_probability(probability, zero_eps)
    amplitudes = np.sqrt(p)
    blocks: dict[str, float] = {}
    for triad in problem.triads:
        amplitude_product = float(
            amplitudes[triad.left]
            * amplitudes[triad.right]
            * amplitudes[triad.out]
        )
        contribution = float(triad.coefficient) * amplitude_product
        key = canonical_orbit_key(problem, triad)
        blocks[key] = blocks.get(key, 0.0) + contribution

    q_value = float(sum(blocks.values()))
    a_value = float(sum(abs(value) for value in blocks.values()))
    positive_q = max(q_value, 0.0)
    dissipation_weights = np.asarray(
        [mode.dissipation_weight for mode in problem.modes], dtype=np.float64
    )
    d_value = float(dissipation_weights @ p)
    viscous_rate = float(2.0 * problem.viscosity * d_value)
    if viscous_rate <= float(zero_eps):
        gamma = None
        envelope_ratio = None
    else:
        gamma = float(positive_q / viscous_rate)
        envelope_ratio = float(a_value / viscous_rate)
    efficiency = float(positive_q / a_value) if a_value > float(zero_eps) else 0.0
    product = (
        float(efficiency * envelope_ratio) if envelope_ratio is not None else None
    )
    identity_residual = (
        abs(float(product) - float(gamma))
        if product is not None and gamma is not None
        else None
    )

    active = p[p > float(zero_eps)]
    entropy = float(-np.sum(active * np.log(active))) if active.size else 0.0
    normalized_entropy = entropy / math.log(float(len(p))) if len(p) > 1 else 0.0
    n_eff = float(1.0 / max(float(np.sum(p * p)), float(zero_eps)))
    shell = np.sqrt(np.maximum(dissipation_weights, 0.0))
    radial_mean = float(shell @ p)
    radial_variance = float(((shell - radial_mean) ** 2) @ p)

    return {
        "q": q_value,
        "a": a_value,
        "positive_q": positive_q,
        "d": d_value,
        "viscous_rate_2nu_d": viscous_rate,
        "positive_efficiency": efficiency,
        "envelope_dissipation_ratio": envelope_ratio,
        "gamma": gamma,
        "product": product,
        "identity_residual": identity_residual,
        "orbit_block_count": len(blocks),
        "n_eff": n_eff,
        "peak_mass": float(np.max(p)),
        "entropy": entropy,
        "normalized_entropy": normalized_entropy,
        "radial_mean": radial_mean,
        "radial_variance": radial_variance,
    }


def feasible(metrics: dict[str, Any], constraints: Constraints) -> bool:
    checks = (
        constraints.max_neff is None or metrics["n_eff"] <= constraints.max_neff,
        constraints.max_radial_variance is None
        or metrics["radial_variance"] <= constraints.max_radial_variance,
        constraints.min_peak_mass is None
        or metrics["peak_mass"] >= constraints.min_peak_mass,
        constraints.max_dissipation is None
        or metrics["d"] <= constraints.max_dissipation,
    )
    return bool(all(checks))


def branch(metrics: dict[str, Any], config: SearchConfig) -> str:
    gamma = metrics.get("gamma")
    if gamma is None:
        return "zero-viscous-denominator"
    if float(gamma) > 1.0 - config.target_eta:
        return "target-counterexample"
    if metrics["positive_efficiency"] <= config.cancellation_cap:
        return "cancellation-depleted"
    envelope_ratio = metrics.get("envelope_dissipation_ratio")
    if envelope_ratio is not None and float(envelope_ratio) <= config.envelope_cap:
        return "envelope-subcritical"
    return "combined-subcritical"


def evaluate_profile(
    problem: Problem,
    probability: Sequence[float],
    config: SearchConfig,
    *,
    profile_id: str,
    source: str,
    extra: dict[str, Any] | None = None,
) -> dict[str, Any]:
    p = normalize_probability(probability, config.zero_eps)
    metrics = profile_metrics(problem, p, config.zero_eps)
    row: dict[str, Any] = {
        "profile_id": profile_id,
        "source": source,
        "probability": [float(value) for value in p],
        **metrics,
        "concentration_constraints_satisfied": feasible(metrics, config.constraints),
        "branch": branch(metrics, config),
    }
    if extra:
        row.update(extra)
    return row
