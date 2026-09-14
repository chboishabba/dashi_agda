#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import numpy as np

OUTPUT_STEM = "continuous_oscillator_lyapunov_diagnostic"
OSCILLATOR_COUNTS = [3, 6, 9]
DEFAULT_SEEDS = [7, 17, 29]
TARGET_FREQUENCIES_HZ = np.array([1.0, 2.5, 4.0], dtype=float)
TARGET_AMPLITUDES = np.array([1.0, 0.7, 0.45], dtype=float)
TARGET_PHASES_RAD = np.array([0.2, -0.8, 1.1], dtype=float)
CANDIDATE_LAWS = [
    "current_gradient",
    "hebbian_style_correlation",
    "oja",
    "kuramoto",
]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Measure finite sampled descent under oscillator update candidates without promoting a global Lyapunov theorem."
    )
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--seeds", type=int, nargs="+", default=DEFAULT_SEEDS)
    parser.add_argument("--steps", type=int, default=200)
    parser.add_argument("--samples", type=int, default=512)
    parser.add_argument("--duration", type=float, default=4.0)
    parser.add_argument("--learning-rate-amplitude", type=float, default=0.02)
    parser.add_argument("--learning-rate-phase", type=float, default=0.01)
    parser.add_argument("--kuramoto-k", type=float, default=1.0)
    return parser.parse_args()


def round_float(value: float) -> float:
    return float(round(float(value), 12))


def wrap_phase(values: np.ndarray) -> np.ndarray:
    return (values + np.pi) % (2.0 * np.pi) - np.pi


def target_waveform(time: np.ndarray) -> np.ndarray:
    args = 2.0 * np.pi * TARGET_FREQUENCIES_HZ[:, None] * time[None, :] + TARGET_PHASES_RAD[:, None]
    return np.sum(TARGET_AMPLITUDES[:, None] * np.cos(args), axis=0)


def initial_state(n: int, seed: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    repeats = n // 3
    rng = np.random.default_rng(seed + 1000 * n)
    frequencies = np.repeat(TARGET_FREQUENCIES_HZ, repeats)
    amplitudes = np.repeat(TARGET_AMPLITUDES / repeats, repeats)
    phases = np.repeat(TARGET_PHASES_RAD, repeats)
    amplitudes = amplitudes * (1.0 + rng.normal(0.0, 0.25, size=n))
    phases = wrap_phase(phases + rng.normal(0.0, 0.55, size=n))
    return frequencies, amplitudes, phases


def waveform_and_basis(
    time: np.ndarray,
    frequencies: np.ndarray,
    amplitudes: np.ndarray,
    phases: np.ndarray,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    args = 2.0 * np.pi * frequencies[:, None] * time[None, :] + phases[:, None]
    cosines = np.cos(args)
    sines = np.sin(args)
    waveform = np.sum(amplitudes[:, None] * cosines, axis=0)
    return waveform, cosines, sines


def energy(
    time: np.ndarray,
    target: np.ndarray,
    frequencies: np.ndarray,
    amplitudes: np.ndarray,
    phases: np.ndarray,
) -> float:
    waveform, _, _ = waveform_and_basis(time, frequencies, amplitudes, phases)
    return float(np.mean((waveform - target) ** 2))


def update(
    law: str,
    time: np.ndarray,
    target: np.ndarray,
    frequencies: np.ndarray,
    amplitudes: np.ndarray,
    phases: np.ndarray,
    lr_a: float,
    lr_phi: float,
    kuramoto_k: float,
) -> tuple[np.ndarray, np.ndarray]:
    waveform, cosines, sines = waveform_and_basis(time, frequencies, amplitudes, phases)
    error = waveform - target

    if law == "current_gradient":
        grad_a = 2.0 * np.mean(error[None, :] * cosines, axis=1)
        grad_phi = 2.0 * np.mean(
            error[None, :] * (-amplitudes[:, None] * sines), axis=1
        )
        new_a = amplitudes - lr_a * grad_a
        new_phi = phases - lr_phi * grad_phi
    elif law == "hebbian_style_correlation":
        delta_a = np.mean(waveform[None, :] * cosines, axis=1)
        new_a = amplitudes + lr_a * delta_a
        new_phi = phases.copy()
    elif law == "oja":
        delta_a = np.mean(
            waveform[None, :] * cosines
            - (waveform[None, :] ** 2) * amplitudes[:, None],
            axis=1,
        )
        new_a = amplitudes + lr_a * delta_a
        new_phi = phases.copy()
    elif law == "kuramoto":
        phase_delta = phases[None, :] - phases[:, None]
        delta_phi = (kuramoto_k / phases.size) * np.sum(np.sin(phase_delta), axis=1)
        new_a = amplitudes.copy()
        new_phi = phases + lr_phi * delta_phi
    else:
        raise ValueError(f"unknown law: {law}")

    return new_a, wrap_phase(new_phi)


def run_candidate(
    law: str,
    time: np.ndarray,
    target: np.ndarray,
    frequencies: np.ndarray,
    amplitudes: np.ndarray,
    phases: np.ndarray,
    steps: int,
    lr_a: float,
    lr_phi: float,
    kuramoto_k: float,
) -> dict[str, Any]:
    a = amplitudes.copy()
    p = phases.copy()
    initial = energy(time, target, frequencies, a, p)
    previous = initial
    nonincrease = 0
    largest_increase = 0.0

    for _ in range(steps):
        a, p = update(
            law,
            time,
            target,
            frequencies,
            a,
            p,
            lr_a,
            lr_phi,
            kuramoto_k,
        )
        current = energy(time, target, frequencies, a, p)
        delta = current - previous
        if delta <= 1.0e-12:
            nonincrease += 1
        largest_increase = max(largest_increase, delta)
        previous = current

    return {
        "steps_observed": steps,
        "initial_energy": round_float(initial),
        "final_energy": round_float(previous),
        "net_energy_change": round_float(previous - initial),
        "nonincrease_steps": nonincrease,
        "nonincrease_fraction": round_float(nonincrease / steps),
        "largest_sampled_increase": round_float(largest_increase),
        "global_lyapunov_proved": False,
        "candidate_native_energy_proved": False,
        "empirical_mechanism_identity_proved": False,
    }


def main() -> int:
    args = parse_args()
    if args.steps <= 0 or args.samples < 32 or args.duration <= 0.0:
        raise SystemExit("steps, samples, and duration must be positive")
    if len(args.seeds) < 1:
        raise SystemExit("at least one seed is required")

    time = np.linspace(0.0, args.duration, args.samples, endpoint=False)
    target = target_waveform(time)
    runs: list[dict[str, Any]] = []

    for n in OSCILLATOR_COUNTS:
        for seed in args.seeds:
            frequencies, amplitudes, phases = initial_state(n, seed)
            candidates = {
                law: run_candidate(
                    law,
                    time,
                    target,
                    frequencies,
                    amplitudes,
                    phases,
                    args.steps,
                    args.learning_rate_amplitude,
                    args.learning_rate_phase,
                    args.kuramoto_k,
                )
                for law in CANDIDATE_LAWS
            }
            runs.append(
                {
                    "oscillator_count": n,
                    "seed": seed,
                    "candidates": candidates,
                }
            )

    payload: dict[str, Any] = {
        "diagnostic": OUTPUT_STEM,
        "schema_version": 1,
        "status": "finite_sample_descent_no_global_theorem",
        "parent_chain": {
            "structural_parent_pr": 896,
            "numerical_parent_pr": 909,
            "update_law_attribution_parent": "ContinuousOscillatorUpdateLawAttributionExact",
            "comparison_parent": "ContinuousOscillatorUpdateLawComparisonReceipt",
        },
        "oscillator_counts": OSCILLATOR_COUNTS,
        "candidate_laws": CANDIDATE_LAWS,
        "energy": {
            "name": "waveform_mse",
            "semantic_truth_metric": False,
            "empirical_adequacy_metric": False,
            "natural_lyapunov_for_all_candidates": False,
        },
        "policy": {
            "same_energy_used_for_comparison": True,
            "candidate_native_energy_claimed": False,
            "sampled_nonincrease_is_global_lyapunov_theorem": False,
            "finite_seed_set_is_universal_state_space": False,
        },
        "runs": runs,
        "promotion": {
            "objective_descent_implies_truth": False,
            "sampled_descent_implies_memory_mechanism": False,
            "sampled_descent_implies_global_stability": False,
            "three_six_nine_stability_ordering": False,
            "hebbian_identity": False,
            "oja_identity": False,
            "kuramoto_identity": False,
        },
    }

    args.out_dir.mkdir(parents=True, exist_ok=True)
    path = args.out_dir / f"{OUTPUT_STEM}.json"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(payload, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
