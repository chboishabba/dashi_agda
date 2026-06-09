#!/usr/bin/env python3
"""
Gray-Scott transfer-operator calibration harness.

This is a pure-stdlib P1 calibration surface for the transfer-operator
formulation.  It intentionally does not claim evidence for Navier-Stokes,
Yang-Mills, or Clay promotion.

The existing Gray-Scott triadic scripts are NumPy-based.  This harness keeps a
10s-safe stdlib path by using a compact synthetic Markov model with Gray-Scott
regime semantics:

  stable spots/worms/solitons -> concentrated invariant measure, low entropy
  mitosis/splitting          -> metastable two-basin transfer, medium entropy
  chaos/broad                -> diffuse transfer, high entropy/leakage

The output metrics are designed to calibrate whether transfer-operator
diagnostics can separate stable/unstable/chaotic pattern regimes before using
the machinery on NS/YM-specific symbols.
"""

from __future__ import annotations

import argparse
import json
import math
import random
from dataclasses import dataclass
from typing import Any


REGIME_LABELS: dict[str, str] = {
    "spots": "stable_pattern",
    "worms": "stable_pattern",
    "solitons": "localized_coherent_pattern",
    "mitosis": "unstable_splitting_pattern",
    "chaos": "chaotic_or_broad_pattern",
}

DEFAULT_PRESETS = ("spots", "mitosis", "chaos")


@dataclass(frozen=True)
class SyntheticRegime:
    name: str
    label: str
    states: int
    coherent_centers: tuple[int, ...]
    metastable_centers: tuple[int, ...]
    stay_weight: float
    basin_weight: float
    neighbor_weight: float
    uniform_weight: float
    leakage_floor: float
    leakage_scale: float
    phase_jitter: float


def regime_config(name: str, states: int) -> SyntheticRegime:
    if states < 8:
        raise ValueError("states must be >= 8")
    label = REGIME_LABELS.get(name, "unclassified_gray_scott_regime")
    mid = states // 2
    if name in {"spots", "worms", "solitons"}:
        return SyntheticRegime(
            name=name,
            label=label,
            states=states,
            coherent_centers=(0,),
            metastable_centers=(0,),
            stay_weight=0.62 if name != "worms" else 0.54,
            basin_weight=0.24 if name != "solitons" else 0.28,
            neighbor_weight=0.10,
            uniform_weight=0.04 if name != "worms" else 0.08,
            leakage_floor=0.07 if name != "worms" else 0.12,
            leakage_scale=0.24,
            phase_jitter=0.18 if name != "worms" else 0.26,
        )
    if name == "mitosis":
        return SyntheticRegime(
            name=name,
            label=label,
            states=states,
            coherent_centers=(0, mid),
            metastable_centers=(0, mid),
            stay_weight=0.35,
            basin_weight=0.30,
            neighbor_weight=0.15,
            uniform_weight=0.20,
            leakage_floor=0.28,
            leakage_scale=0.38,
            phase_jitter=0.48,
        )
    if name == "chaos":
        return SyntheticRegime(
            name=name,
            label=label,
            states=states,
            coherent_centers=tuple(range(states)),
            metastable_centers=tuple(range(states)),
            stay_weight=0.08,
            basin_weight=0.04,
            neighbor_weight=0.08,
            uniform_weight=0.80,
            leakage_floor=0.58,
            leakage_scale=0.34,
            phase_jitter=0.95,
        )
    return SyntheticRegime(
        name=name,
        label=label,
        states=states,
        coherent_centers=(0,),
        metastable_centers=(0,),
        stay_weight=0.30,
        basin_weight=0.22,
        neighbor_weight=0.18,
        uniform_weight=0.30,
        leakage_floor=0.32,
        leakage_scale=0.36,
        phase_jitter=0.55,
    )


def circular_distance(a: int, b: int, n: int) -> int:
    raw = abs(a - b) % n
    return min(raw, n - raw)


def normalize(row: list[float]) -> list[float]:
    total = sum(row)
    if total <= 0.0:
        return [1.0 / len(row) for _ in row]
    return [x / total for x in row]


def transition_matrix(config: SyntheticRegime) -> list[list[float]]:
    n = config.states
    rows: list[list[float]] = []
    sigma = max(1.0, n / 18.0)
    for i in range(n):
        row = [config.uniform_weight / n for _ in range(n)]
        row[i] += config.stay_weight
        row[(i - 1) % n] += 0.5 * config.neighbor_weight
        row[(i + 1) % n] += 0.5 * config.neighbor_weight

        nearest = min(config.metastable_centers, key=lambda c: circular_distance(i, c, n))
        if config.name == "mitosis" and circular_distance(i, nearest, n) <= max(2, n // 12):
            other = config.metastable_centers[1] if nearest == config.metastable_centers[0] else config.metastable_centers[0]
            row[other] += 0.32 * config.basin_weight
            row[nearest] += 0.68 * config.basin_weight
        else:
            for center in config.metastable_centers:
                dist = circular_distance(i, center, n)
                row[center] += config.basin_weight * math.exp(-(dist * dist) / (2.0 * sigma * sigma))
        rows.append(normalize(row))
    return rows


def power_stationary(matrix: list[list[float]], iterations: int, tolerance: float) -> tuple[list[float], int, float]:
    n = len(matrix)
    dist = [1.0 / n for _ in range(n)]
    last_delta = 0.0
    for step in range(1, iterations + 1):
        nxt = [0.0 for _ in range(n)]
        for i, mass in enumerate(dist):
            if mass == 0.0:
                continue
            row = matrix[i]
            for j, p in enumerate(row):
                nxt[j] += mass * p
        last_delta = sum(abs(a - b) for a, b in zip(nxt, dist))
        dist = nxt
        if last_delta <= tolerance:
            return dist, step, last_delta
    return dist, iterations, last_delta


def entropy_normalized(weights: list[float]) -> float:
    positive = [w for w in weights if w > 0.0]
    if len(positive) <= 1:
        return 0.0
    total = sum(positive)
    entropy = -sum((w / total) * math.log(w / total) for w in positive)
    return entropy / math.log(len(weights))


def transition_entropy(matrix: list[list[float]], stationary: list[float]) -> float:
    return sum(weight * entropy_normalized(row) for weight, row in zip(stationary, matrix))


def invariant_concentration(stationary: list[float], top_fraction: float) -> float:
    n = len(stationary)
    take = max(1, int(math.ceil(n * top_fraction)))
    return sum(sorted(stationary, reverse=True)[:take])


def l2_action_on_zero_mean(matrix: list[list[float]], vector: list[float]) -> float:
    n = len(matrix)
    mean = sum(vector) / n
    centered = [x - mean for x in vector]
    out = [0.0 for _ in range(n)]
    for i, x in enumerate(centered):
        for j, p in enumerate(matrix[i]):
            out[j] += x * p
    out_mean = sum(out) / n
    out = [x - out_mean for x in out]
    before = math.sqrt(sum(x * x for x in centered))
    after = math.sqrt(sum(x * x for x in out))
    if before <= 0.0:
        return 0.0
    return after / before


def spectral_gap_proxy(matrix: list[list[float]], samples: int, seed: int) -> dict[str, float]:
    rng = random.Random(seed)
    contractions: list[float] = []
    n = len(matrix)
    basis = [
        [math.cos(2.0 * math.pi * i / n) for i in range(n)],
        [math.sin(2.0 * math.pi * i / n) for i in range(n)],
        [math.cos(4.0 * math.pi * i / n) for i in range(n)],
        [math.sin(4.0 * math.pi * i / n) for i in range(n)],
    ]
    for vector in basis:
        contractions.append(l2_action_on_zero_mean(matrix, vector))
    for _ in range(max(0, samples - len(basis))):
        contractions.append(l2_action_on_zero_mean(matrix, [rng.uniform(-1.0, 1.0) for _ in range(n)]))
    second_proxy = max(contractions) if contractions else 0.0
    return {
        "second_eigenvalue_modulus_proxy": second_proxy,
        "spectral_gap_proxy": max(0.0, 1.0 - second_proxy),
        "mean_zero_mode_contraction": sum(contractions) / len(contractions) if contractions else 0.0,
    }


def leakage_by_state(config: SyntheticRegime) -> list[float]:
    n = config.states
    values: list[float] = []
    for i in range(n):
        nearest = min(config.coherent_centers, key=lambda c: circular_distance(i, c, n))
        d = circular_distance(i, nearest, n) / max(1.0, n / 2.0)
        jitter = config.phase_jitter * (0.5 + 0.5 * math.sin(2.0 * math.pi * (i + 0.25) / n))
        value = config.leakage_floor + config.leakage_scale * d + 0.18 * jitter
        values.append(max(0.0, min(1.0, value)))
    return values


def transition_samples(
    matrix: list[list[float]],
    leakage: list[float],
    *,
    steps: int,
    seed: int,
) -> dict[str, Any]:
    rng = random.Random(seed)
    n = len(matrix)
    state = rng.randrange(n)
    visits = [0 for _ in range(n)]
    leak_values: list[float] = []
    transition_surprise: list[float] = []
    for _ in range(steps):
        visits[state] += 1
        leak_values.append(leakage[state])
        row = matrix[state]
        r = rng.random()
        acc = 0.0
        nxt = n - 1
        for j, p in enumerate(row):
            acc += p
            if r <= acc:
                nxt = j
                break
        transition_surprise.append(-math.log(max(row[nxt], 1e-15)))
        state = nxt
    return {
        "steps": steps,
        "visit_entropy_normalized": entropy_normalized([float(v) for v in visits]),
        "sampled_leakage_mean": sum(leak_values) / len(leak_values) if leak_values else 0.0,
        "sampled_transition_surprise_mean": (
            sum(transition_surprise) / len(transition_surprise) if transition_surprise else 0.0
        ),
        "visited_states": sum(1 for v in visits if v > 0),
    }


def classify_metrics(
    *,
    concentration: float,
    entropy: float,
    leakage: float,
    spectral_gap: float,
    visits_entropy: float,
) -> str:
    if concentration >= 0.20 and entropy <= 0.35 and leakage <= 0.28:
        return "stable_transfer_concentrated_low_leakage"
    if entropy >= 0.72 and leakage >= 0.55 and concentration <= 0.45:
        return "chaotic_transfer_diffuse_high_leakage"
    if 0.35 <= leakage <= 0.52 and 0.42 <= entropy <= 0.70:
        return "metastable_or_splitting_transfer"
    if spectral_gap < 0.18 and visits_entropy < 0.78:
        return "metastable_or_splitting_transfer"
    return "mixed_transfer_calibration"


def run_regime(
    preset: str,
    *,
    states: int,
    iterations: int,
    samples: int,
    trajectory_steps: int,
    seed: int,
) -> dict[str, Any]:
    config = regime_config(preset, states)
    matrix = transition_matrix(config)
    stationary, stationary_iterations, stationary_delta = power_stationary(
        matrix, iterations=iterations, tolerance=1e-12
    )
    leakage = leakage_by_state(config)
    concentration = invariant_concentration(stationary, top_fraction=0.10)
    top1 = max(stationary) if stationary else 0.0
    trans_entropy = transition_entropy(matrix, stationary)
    invariant_entropy = entropy_normalized(stationary)
    leakage_mean = sum(w * l for w, l in zip(stationary, leakage))
    spectral = spectral_gap_proxy(matrix, samples=samples, seed=seed + 101)
    trajectory = transition_samples(matrix, leakage, steps=trajectory_steps, seed=seed + 202)
    calibration_score = max(
        0.0,
        min(
            1.0,
            0.28 * concentration
            + 0.20 * (1.0 - trans_entropy)
            + 0.18 * (1.0 - leakage_mean)
            + 0.16 * spectral["spectral_gap_proxy"]
            + 0.10 * (1.0 - invariant_entropy)
            + 0.08 * (1.0 - trajectory["visit_entropy_normalized"]),
        ),
    )
    return {
        "preset": preset,
        "regime_label": config.label,
        "ok": True,
        "promotion": False,
        "clay_promotion": False,
        "model": {
            "kind": "synthetic_gray_scott_transfer_operator",
            "stdlib_only": True,
            "existing_numpy_harness_used": False,
            "existing_harness_reason": (
                "gray_scott_triadic_defect_harness.py imports numpy at module import; "
                "this lane requires a pure-stdlib 10s-safe calibration path"
            ),
            "states": states,
            "coherent_centers": list(config.coherent_centers),
            "metastable_centers": list(config.metastable_centers),
        },
        "metrics": {
            "invariant_concentration_top10": concentration,
            "invariant_top1_mass": top1,
            "invariant_entropy_normalized": invariant_entropy,
            "transition_entropy_normalized": trans_entropy,
            "leakage_proxy_stationary_mean": leakage_mean,
            "spectral_gap_proxy": spectral["spectral_gap_proxy"],
            "second_eigenvalue_modulus_proxy": spectral["second_eigenvalue_modulus_proxy"],
            "mean_zero_mode_contraction": spectral["mean_zero_mode_contraction"],
            "stationary_iterations": stationary_iterations,
            "stationary_l1_delta": stationary_delta,
            "trajectory_visit_entropy_normalized": trajectory["visit_entropy_normalized"],
            "trajectory_sampled_leakage_mean": trajectory["sampled_leakage_mean"],
            "trajectory_sampled_transition_surprise_mean": trajectory[
                "sampled_transition_surprise_mean"
            ],
            "trajectory_visited_states": trajectory["visited_states"],
            "calibration_score": calibration_score,
        },
        "classification": classify_metrics(
            concentration=concentration,
            entropy=trans_entropy,
            leakage=leakage_mean,
            spectral_gap=spectral["spectral_gap_proxy"],
            visits_entropy=trajectory["visit_entropy_normalized"],
        ),
    }


def parse_presets(value: str) -> list[str]:
    presets = [part.strip() for part in value.split(",") if part.strip()]
    if not presets:
        raise argparse.ArgumentTypeError("expected at least one preset")
    return presets


def aggregate(cases: list[dict[str, Any]]) -> dict[str, Any]:
    by_label: dict[str, list[dict[str, Any]]] = {}
    for case in cases:
        by_label.setdefault(case["regime_label"], []).append(case)
    stable = [
        case
        for case in cases
        if case["regime_label"] in {"stable_pattern", "localized_coherent_pattern"}
    ]
    unstable = [case for case in cases if case["regime_label"] == "unstable_splitting_pattern"]
    chaotic = [case for case in cases if case["regime_label"] == "chaotic_or_broad_pattern"]

    def mean_metric(rows: list[dict[str, Any]], key: str) -> float | None:
        if not rows:
            return None
        return sum(float(row["metrics"][key]) for row in rows) / len(rows)

    stable_concentration = mean_metric(stable, "invariant_concentration_top10")
    chaotic_concentration = mean_metric(chaotic, "invariant_concentration_top10")
    stable_entropy = mean_metric(stable, "transition_entropy_normalized")
    chaotic_entropy = mean_metric(chaotic, "transition_entropy_normalized")
    stable_leakage = mean_metric(stable, "leakage_proxy_stationary_mean")
    chaotic_leakage = mean_metric(chaotic, "leakage_proxy_stationary_mean")

    separation_checks = {
        "stable_more_concentrated_than_chaos": (
            stable_concentration is not None
            and chaotic_concentration is not None
            and stable_concentration > chaotic_concentration
        ),
        "stable_lower_entropy_than_chaos": (
            stable_entropy is not None
            and chaotic_entropy is not None
            and stable_entropy < chaotic_entropy
        ),
        "stable_lower_leakage_than_chaos": (
            stable_leakage is not None
            and chaotic_leakage is not None
            and stable_leakage < chaotic_leakage
        ),
        "unstable_present": bool(unstable),
    }
    passed = sum(1 for value in separation_checks.values() if value)
    return {
        "case_count": len(cases),
        "labels": {label: len(rows) for label, rows in sorted(by_label.items())},
        "mean_metrics": {
            "stable_invariant_concentration_top10": stable_concentration,
            "chaotic_invariant_concentration_top10": chaotic_concentration,
            "stable_transition_entropy_normalized": stable_entropy,
            "chaotic_transition_entropy_normalized": chaotic_entropy,
            "stable_leakage_proxy_stationary_mean": stable_leakage,
            "chaotic_leakage_proxy_stationary_mean": chaotic_leakage,
        },
        "separation_checks": separation_checks,
        "separation_score": passed / len(separation_checks),
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Pure-stdlib Gray-Scott transfer-operator calibration harness"
    )
    parser.add_argument("--json", action="store_true", help="emit JSON")
    parser.add_argument("--quick", action="store_true", help="10s-safe preset/settings")
    parser.add_argument("--presets", type=parse_presets, default=None)
    parser.add_argument("--states", type=int, default=48)
    parser.add_argument("--iterations", type=int, default=4000)
    parser.add_argument("--samples", type=int, default=64)
    parser.add_argument("--trajectory-steps", type=int, default=1600)
    parser.add_argument("--seed", type=int, default=0)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    presets = args.presets or list(DEFAULT_PRESETS)
    states = args.states
    iterations = args.iterations
    samples = args.samples
    trajectory_steps = args.trajectory_steps
    if args.quick:
        presets = args.presets or list(DEFAULT_PRESETS)
        states = min(states, 36)
        iterations = min(iterations, 1200)
        samples = min(samples, 32)
        trajectory_steps = min(trajectory_steps, 700)

    cases = [
        run_regime(
            preset,
            states=states,
            iterations=iterations,
            samples=samples,
            trajectory_steps=trajectory_steps,
            seed=args.seed + 997 * idx,
        )
        for idx, preset in enumerate(presets)
    ]
    report = {
        "harness": "gray_scott_transfer_operator_calibration",
        "ok": all(case["ok"] for case in cases),
        "promotion": False,
        "clay_promotion": False,
        "quick": bool(args.quick),
        "inputs": {
            "presets": presets,
            "states": states,
            "iterations": iterations,
            "samples": samples,
            "trajectory_steps": trajectory_steps,
            "seed": args.seed,
        },
        "cases": cases,
        "aggregate": aggregate(cases),
        "interpretation": {
            "scope": "P1 calibration only",
            "claim": (
                "transfer metrics should separate synthetic stable, unstable, and chaotic "
                "Gray-Scott-like regimes before being trusted as a measurement layer"
            ),
            "clay_relevance": "none_direct",
        },
    }
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        agg = report["aggregate"]
        print("Gray-Scott transfer-operator calibration")
        print(f"ok={report['ok']} clay_promotion={report['clay_promotion']}")
        print(f"separation_score={agg['separation_score']:.3f}")
        for case in cases:
            metrics = case["metrics"]
            print(
                f"{case['preset']}: {case['classification']} "
                f"conc={metrics['invariant_concentration_top10']:.3f} "
                f"H={metrics['transition_entropy_normalized']:.3f} "
                f"leak={metrics['leakage_proxy_stationary_mean']:.3f}"
            )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
