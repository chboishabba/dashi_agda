#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import numpy as np

OUTPUT_STEM = "continuous_oscillator_identifiability"
OSCILLATOR_COUNTS = [3, 6, 9]
DEFAULT_SEEDS = [7, 17, 29]
TARGET_FREQUENCIES_HZ = np.array([1.0, 2.5, 4.0], dtype=float)
TARGET_AMPLITUDES = np.array([1.0, 0.7, 0.45], dtype=float)
TARGET_PHASES_RAD = np.array([0.2, -0.8, 1.1], dtype=float)
QUERY_FAMILY = ["waveform", "frequency", "amplitude", "phase", "hidden_state"]
FREQUENCY_BOUNDS_HZ = (0.5, 4.5)
GAUGE_POLICY = {
    "phase_periodicity_mod_2pi": True,
    "permutation_within_target_group": True,
    "matching_rule": "nearest_target_frequency_then_frequency_order",
    "global_time_origin_quotiented": False,
    "amplitude_sign_phase_equivalence_quotiented": False,
}
FAIL_CLOSED_FLAGS = {
    "neuroscience_interpretation_promoted": False,
    "memory_mechanism_promoted": False,
    "hebbian_identity_promoted": False,
    "oja_identity_promoted": False,
    "kuramoto_identity_promoted": False,
    "cognitive_dissonance_identity_promoted": False,
    "empirical_brain_fit_promoted": False,
    "three_six_nine_superiority_promoted": False,
    "quantum_interpretation_promoted": False,
    "global_identifiability_promoted": False,
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run bounded synthetic oscillator identifiability diagnostics.")
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--seeds", type=int, nargs="+", default=DEFAULT_SEEDS)
    parser.add_argument("--max-steps", type=int, default=800)
    parser.add_argument("--samples", type=int, default=768)
    parser.add_argument("--duration", type=float, default=4.0)
    parser.add_argument("--train-fraction", type=float, default=0.7)
    parser.add_argument("--learning-rate-amplitude", type=float, default=0.06)
    parser.add_argument("--learning-rate-phase", type=float, default=0.025)
    parser.add_argument("--learning-rate-frequency", type=float, default=0.002)
    parser.add_argument("--observable-tolerance", type=float, default=1.0e-4)
    parser.add_argument("--parameter-tolerance", type=float, default=5.0e-2)
    return parser.parse_args()


def round_float(value: float) -> float:
    return float(round(float(value), 12))


def wrap_phase(delta: np.ndarray) -> np.ndarray:
    return (delta + np.pi) % (2.0 * np.pi) - np.pi


def target_waveform(time: np.ndarray) -> np.ndarray:
    args = 2.0 * np.pi * TARGET_FREQUENCIES_HZ[:, None] * time[None, :] + TARGET_PHASES_RAD[:, None]
    return np.sum(TARGET_AMPLITUDES[:, None] * np.cos(args), axis=0)


def layout(n: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    repeats = n // 3
    return (
        np.repeat(TARGET_FREQUENCIES_HZ, repeats),
        np.repeat(TARGET_AMPLITUDES / repeats, repeats),
        np.repeat(TARGET_PHASES_RAD, repeats),
    )


def synthesize(time: np.ndarray, frequencies: np.ndarray, amplitudes: np.ndarray, phases: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    args = 2.0 * np.pi * frequencies[:, None] * time[None, :] + phases[:, None]
    cosines = np.cos(args)
    sines = np.sin(args)
    return np.sum(amplitudes[:, None] * cosines, axis=0), cosines, sines


def canonical_recovery(n: int, frequencies: np.ndarray, amplitudes: np.ndarray, phases: np.ndarray) -> dict[str, Any]:
    repeats = n // 3
    recovered_f: list[float] = []
    recovered_a: list[float] = []
    recovered_phi: list[float] = []
    for target_f in TARGET_FREQUENCIES_HZ:
        order = np.argsort(np.abs(frequencies - target_f), kind="stable")[:repeats]
        order = order[np.argsort(frequencies[order], kind="stable")]
        weights = np.abs(amplitudes[order])
        weight_sum = float(np.sum(weights))
        recovered_f.append(float(np.mean(frequencies[order])))
        recovered_a.append(float(np.sum(amplitudes[order])))
        if weight_sum > 1.0e-12:
            phasor = np.sum(weights * np.exp(1j * phases[order])) / weight_sum
            recovered_phi.append(float(np.angle(phasor)))
        else:
            recovered_phi.append(float(np.angle(np.mean(np.exp(1j * phases[order])))))
    f = np.asarray(recovered_f)
    a = np.asarray(recovered_a)
    p = np.asarray(recovered_phi)
    df = f - TARGET_FREQUENCIES_HZ
    da = a - TARGET_AMPLITUDES
    dp = wrap_phase(p - TARGET_PHASES_RAD)
    distance = float(np.sqrt(np.mean(df * df) + np.mean(da * da) + np.mean(dp * dp)))
    return {
        "gauge_normalized": True,
        "canonical_frequencies_hz": [round_float(x) for x in f],
        "canonical_amplitudes": [round_float(x) for x in a],
        "canonical_phases_rad": [round_float(x) for x in p],
        "frequency_rmse_hz": round_float(np.sqrt(np.mean(df * df))),
        "amplitude_rmse": round_float(np.sqrt(np.mean(da * da))),
        "phase_rmse_rad": round_float(np.sqrt(np.mean(dp * dp))),
        "canonical_parameter_distance": round_float(distance),
    }


def optimize(n: int, seed: int, train_time: np.ndarray, train_target: np.ndarray, heldout_time: np.ndarray, heldout_target: np.ndarray, max_steps: int, lr_a: float, lr_phi: float, lr_f: float, observable_tolerance: float, parameter_tolerance: float) -> dict[str, Any]:
    rng = np.random.default_rng(seed + 1000 * n)
    frequencies, amplitudes, phases = layout(n)
    frequencies += rng.normal(0.0, 0.12, size=n)
    amplitudes *= 1.0 + rng.normal(0.0, 0.25, size=n)
    phases += rng.normal(0.0, 0.55, size=n)
    low, high = FREQUENCY_BOUNDS_HZ
    for _ in range(max_steps):
        waveform, cosines, sines = synthesize(train_time, frequencies, amplitudes, phases)
        error = waveform - train_target
        grad_a = 2.0 * np.mean(error[None, :] * cosines, axis=1)
        grad_phi = 2.0 * np.mean(error[None, :] * (-amplitudes[:, None] * sines), axis=1)
        grad_f = 2.0 * np.mean(error[None, :] * (-amplitudes[:, None] * sines) * (2.0 * np.pi * train_time[None, :]), axis=1)
        amplitudes -= lr_a * grad_a
        phases = wrap_phase(phases - lr_phi * grad_phi)
        frequencies = np.clip(frequencies - lr_f * grad_f, low, high)
    train_waveform, _, _ = synthesize(train_time, frequencies, amplitudes, phases)
    heldout_waveform, _, _ = synthesize(heldout_time, frequencies, amplitudes, phases)
    train_loss = float(np.mean((train_waveform - train_target) ** 2))
    heldout_loss = float(np.mean((heldout_waveform - heldout_target) ** 2))
    recovery = canonical_recovery(n, frequencies, amplitudes, phases)
    near_collision = bool(heldout_loss <= observable_tolerance and recovery["canonical_parameter_distance"] > parameter_tolerance)
    query_diagnostics = {
        "waveform": {"consumer": "heldout_reconstruction", "error": round_float(heldout_loss), "exact_factorability_proved": False},
        "frequency": {"consumer": "canonical_parameter_recovery", "error": recovery["frequency_rmse_hz"], "exact_factorability_proved": False},
        "amplitude": {"consumer": "canonical_parameter_recovery", "error": recovery["amplitude_rmse"], "exact_factorability_proved": False},
        "phase": {"consumer": "gauge_normalized_parameter_recovery", "error": recovery["phase_rmse_rad"], "exact_factorability_proved": False},
        "hidden_state": {"consumer": "canonical_hidden_state_recovery", "error": recovery["canonical_parameter_distance"], "exact_factorability_proved": False},
    }
    return {
        "oscillator_count": n,
        "seed": seed,
        "frequencies_learnable": True,
        "train_fit_loss": round_float(train_loss),
        "heldout_fit_loss": round_float(heldout_loss),
        "learned_frequencies_hz": [round_float(x) for x in frequencies],
        "learned_amplitudes": [round_float(x) for x in amplitudes],
        "learned_phases_rad": [round_float(x) for x in phases],
        "recovery": recovery,
        "near_collision_diagnostic": {
            "observed": near_collision,
            "observable_distance": round_float(heldout_loss),
            "canonical_parameter_distance": recovery["canonical_parameter_distance"],
            "exact_nonfactorability_proved": False,
        },
        "query_diagnostics": query_diagnostics,
        "classification": "optimizationUnresolved",
    }


def main() -> int:
    args = parse_args()
    if args.max_steps <= 0 or args.samples < 32 or args.duration <= 0.0:
        raise SystemExit("max-steps, samples, and duration must be positive")
    if not 0.0 < args.train_fraction < 1.0:
        raise SystemExit("train-fraction must lie strictly between zero and one")
    time = np.linspace(0.0, args.duration, args.samples, endpoint=False)
    target = target_waveform(time)
    split = max(1, min(args.samples - 1, int(args.samples * args.train_fraction)))
    train_time, heldout_time = time[:split], time[split:]
    train_target, heldout_target = target[:split], target[split:]
    runs = [
        optimize(n, seed, train_time, train_target, heldout_time, heldout_target, args.max_steps, args.learning_rate_amplitude, args.learning_rate_phase, args.learning_rate_frequency, args.observable_tolerance, args.parameter_tolerance)
        for n in OSCILLATOR_COUNTS for seed in args.seeds
    ]
    near_count = sum(int(run["near_collision_diagnostic"]["observed"]) for run in runs)
    payload: dict[str, Any] = {
        "diagnostic": OUTPUT_STEM,
        "schema_version": 2,
        "status": "synthetic_identifiability_no_promotion",
        "parent_chain": {"structural_parent_pr": 896, "numerical_parent_pr": 909, "parent_following": True},
        "oscillator_counts": OSCILLATOR_COUNTS,
        "query_family": QUERY_FAMILY,
        "gauge_policy": GAUGE_POLICY,
        "design": {
            "frequencies_learnable": True,
            "frequency_bounds_hz": list(FREQUENCY_BOUNDS_HZ),
            "train_fraction": args.train_fraction,
            "frozen_before_holdout": True,
            "observable_tolerance": args.observable_tolerance,
            "parameter_tolerance": args.parameter_tolerance,
            "max_steps": args.max_steps,
            "learning_rates": {"amplitude": args.learning_rate_amplitude, "phase": args.learning_rate_phase, "frequency": args.learning_rate_frequency},
        },
        "target": {"frequencies_hz": [round_float(x) for x in TARGET_FREQUENCIES_HZ], "amplitudes": [round_float(x) for x in TARGET_AMPLITUDES], "phases_rad": [round_float(x) for x in TARGET_PHASES_RAD]},
        "comparison_policy": {"same_target_support": True, "ranking_required": False, "nine_superiority_assumed": False, "query_adequacy_is_relative": True},
        "runs": runs,
        "near_collision_summary": {"status": "observed" if near_count else "not_observed", "count": near_count, "run_count": len(runs), "exact_nonfactorability_proved": False},
        "promotion": {"state": "blocked", "flags": FAIL_CLOSED_FLAGS},
        "formal_boundary": {"numerical_near_collision_is_exact_nonfactorability_proof": False, "waveform_adequacy_implies_hidden_state_adequacy": False, "optimizer_failure_implies_nonidentifiability": False},
    }
    args.out_dir.mkdir(parents=True, exist_ok=True)
    path = args.out_dir / f"{OUTPUT_STEM}.json"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(payload, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
