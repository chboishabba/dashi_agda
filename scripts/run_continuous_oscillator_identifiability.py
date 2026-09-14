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
NOISE_LEVELS = [0.0, 0.02, 0.05]
SEPARATION_FACTORS = [1.0, 0.6, 0.3]
SPECTRAL_TRANSFER_OFFSET_HZ = 0.18
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
    parser = argparse.ArgumentParser(
        description="Run bounded synthetic oscillator identifiability diagnostics."
    )
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--seeds", type=int, nargs="+", default=DEFAULT_SEEDS)
    parser.add_argument("--max-steps", type=int, default=800)
    parser.add_argument("--null-steps", type=int, default=120)
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


def build_waveform(
    time: np.ndarray,
    frequencies: np.ndarray,
    amplitudes: np.ndarray,
    phases: np.ndarray,
) -> np.ndarray:
    args = 2.0 * np.pi * frequencies[:, None] * time[None, :] + phases[:, None]
    return np.sum(amplitudes[:, None] * np.cos(args), axis=0)


def target_waveform(time: np.ndarray) -> np.ndarray:
    return build_waveform(
        time, TARGET_FREQUENCIES_HZ, TARGET_AMPLITUDES, TARGET_PHASES_RAD
    )


def layout(
    n: int,
    target_frequencies: np.ndarray,
    target_amplitudes: np.ndarray,
    target_phases: np.ndarray,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    repeats = n // 3
    return (
        np.repeat(target_frequencies, repeats),
        np.repeat(target_amplitudes / repeats, repeats),
        np.repeat(target_phases, repeats),
    )


def synthesize(
    time: np.ndarray,
    frequencies: np.ndarray,
    amplitudes: np.ndarray,
    phases: np.ndarray,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    args = 2.0 * np.pi * frequencies[:, None] * time[None, :] + phases[:, None]
    cosines = np.cos(args)
    sines = np.sin(args)
    return np.sum(amplitudes[:, None] * cosines, axis=0), cosines, sines


def canonical_recovery(
    n: int,
    frequencies: np.ndarray,
    amplitudes: np.ndarray,
    phases: np.ndarray,
    target_frequencies: np.ndarray,
    target_amplitudes: np.ndarray,
    target_phases: np.ndarray,
) -> dict[str, Any]:
    repeats = n // 3
    recovered_f: list[float] = []
    recovered_a: list[float] = []
    recovered_phi: list[float] = []
    unused = set(range(n))
    for target_f in target_frequencies:
        candidates = sorted(unused, key=lambda idx: abs(float(frequencies[idx] - target_f)))
        chosen = candidates[:repeats]
        unused.difference_update(chosen)
        order = np.asarray(sorted(chosen, key=lambda idx: float(frequencies[idx])), dtype=int)
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
    df = f - target_frequencies
    da = a - target_amplitudes
    dp = wrap_phase(p - target_phases)
    distance = float(
        np.sqrt(np.mean(df * df) + np.mean(da * da) + np.mean(dp * dp))
    )
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


def optimize(
    n: int,
    seed: int,
    train_time: np.ndarray,
    train_target: np.ndarray,
    heldout_time: np.ndarray,
    heldout_target: np.ndarray,
    max_steps: int,
    lr_a: float,
    lr_phi: float,
    lr_f: float,
    observable_tolerance: float,
    parameter_tolerance: float,
    target_frequencies: np.ndarray = TARGET_FREQUENCIES_HZ,
    target_amplitudes: np.ndarray = TARGET_AMPLITUDES,
    target_phases: np.ndarray = TARGET_PHASES_RAD,
) -> dict[str, Any]:
    rng = np.random.default_rng(seed + 1000 * n)
    frequencies, amplitudes, phases = layout(
        n, target_frequencies, target_amplitudes, target_phases
    )
    frequencies += rng.normal(0.0, 0.12, size=n)
    amplitudes *= 1.0 + rng.normal(0.0, 0.25, size=n)
    phases += rng.normal(0.0, 0.55, size=n)
    low, high = FREQUENCY_BOUNDS_HZ

    for _ in range(max_steps):
        waveform, cosines, sines = synthesize(
            train_time, frequencies, amplitudes, phases
        )
        error = waveform - train_target
        grad_a = 2.0 * np.mean(error[None, :] * cosines, axis=1)
        grad_phi = 2.0 * np.mean(
            error[None, :] * (-amplitudes[:, None] * sines), axis=1
        )
        grad_f = 2.0 * np.mean(
            error[None, :]
            * (-amplitudes[:, None] * sines)
            * (2.0 * np.pi * train_time[None, :]),
            axis=1,
        )
        amplitudes -= lr_a * grad_a
        phases = wrap_phase(phases - lr_phi * grad_phi)
        frequencies = np.clip(frequencies - lr_f * grad_f, low, high)

    train_waveform, _, _ = synthesize(
        train_time, frequencies, amplitudes, phases
    )
    heldout_waveform, _, _ = synthesize(
        heldout_time, frequencies, amplitudes, phases
    )
    train_loss = float(np.mean((train_waveform - train_target) ** 2))
    heldout_loss = float(np.mean((heldout_waveform - heldout_target) ** 2))
    recovery = canonical_recovery(
        n,
        frequencies,
        amplitudes,
        phases,
        target_frequencies,
        target_amplitudes,
        target_phases,
    )
    near_collision = bool(
        heldout_loss <= observable_tolerance
        and recovery["canonical_parameter_distance"] > parameter_tolerance
    )
    query_diagnostics = {
        "waveform": {
            "consumer": "heldout_reconstruction",
            "error": round_float(heldout_loss),
            "exact_factorability_proved": False,
        },
        "frequency": {
            "consumer": "canonical_parameter_recovery",
            "error": recovery["frequency_rmse_hz"],
            "exact_factorability_proved": False,
        },
        "amplitude": {
            "consumer": "canonical_parameter_recovery",
            "error": recovery["amplitude_rmse"],
            "exact_factorability_proved": False,
        },
        "phase": {
            "consumer": "gauge_normalized_parameter_recovery",
            "error": recovery["phase_rmse_rad"],
            "exact_factorability_proved": False,
        },
        "hidden_state": {
            "consumer": "canonical_hidden_state_recovery",
            "error": recovery["canonical_parameter_distance"],
            "exact_factorability_proved": False,
        },
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
            "canonical_parameter_distance": recovery[
                "canonical_parameter_distance"
            ],
            "exact_nonfactorability_proved": False,
        },
        "query_diagnostics": query_diagnostics,
        "classification": "optimizationUnresolved",
    }


def split_target(
    time: np.ndarray,
    train_fraction: float,
    frequencies: np.ndarray,
    amplitudes: np.ndarray,
    phases: np.ndarray,
    noise_sigma: float = 0.0,
    noise_seed: int = 0,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    target = build_waveform(time, frequencies, amplitudes, phases)
    if noise_sigma > 0.0:
        rng = np.random.default_rng(noise_seed)
        target = target + rng.normal(0.0, noise_sigma, size=target.shape)
    split = max(1, min(time.size - 1, int(time.size * train_fraction)))
    return time[:split], target[:split], time[split:], target[split:]


def run_null_fit(
    n: int,
    seed: int,
    time: np.ndarray,
    train_fraction: float,
    frequencies: np.ndarray,
    amplitudes: np.ndarray,
    phases: np.ndarray,
    noise_sigma: float,
    null_steps: int,
    args: argparse.Namespace,
) -> dict[str, Any]:
    train_time, train_target, heldout_time, heldout_target = split_target(
        time,
        train_fraction,
        frequencies,
        amplitudes,
        phases,
        noise_sigma=noise_sigma,
        noise_seed=seed + 7919 * n,
    )
    return optimize(
        n,
        seed,
        train_time,
        train_target,
        heldout_time,
        heldout_target,
        null_steps,
        args.learning_rate_amplitude,
        args.learning_rate_phase,
        args.learning_rate_frequency,
        args.observable_tolerance,
        args.parameter_tolerance,
        frequencies,
        amplitudes,
        phases,
    )


def build_falsification_ladder(
    time: np.ndarray,
    args: argparse.Namespace,
    runs: list[dict[str, Any]],
) -> dict[str, Any]:
    by_count: dict[str, Any] = {}
    first_seed = int(args.seeds[0])
    center = float(np.mean(TARGET_FREQUENCIES_HZ))

    for n in OSCILLATOR_COUNTS:
        base_runs = [run for run in runs if run["oscillator_count"] == n]
        restart_losses = [float(run["heldout_fit_loss"]) for run in base_runs]
        restart_parameters = [
            float(run["recovery"]["canonical_parameter_distance"])
            for run in base_runs
        ]

        noise_results: list[dict[str, Any]] = []
        for level in NOISE_LEVELS:
            fit = run_null_fit(
                n,
                first_seed + int(level * 10000),
                time,
                args.train_fraction,
                TARGET_FREQUENCIES_HZ,
                TARGET_AMPLITUDES,
                TARGET_PHASES_RAD,
                level,
                args.null_steps,
                args,
            )
            noise_results.append(
                {
                    "sigma": level,
                    "heldout_fit_loss": fit["heldout_fit_loss"],
                    "hidden_state_error": fit["recovery"][
                        "canonical_parameter_distance"
                    ],
                }
            )

        separation_results: list[dict[str, Any]] = []
        for factor in SEPARATION_FACTORS:
            frequencies = center + factor * (TARGET_FREQUENCIES_HZ - center)
            fit = run_null_fit(
                n,
                first_seed + int(factor * 1000) + 101,
                time,
                args.train_fraction,
                frequencies,
                TARGET_AMPLITUDES,
                TARGET_PHASES_RAD,
                0.0,
                args.null_steps,
                args,
            )
            separation_results.append(
                {
                    "factor": factor,
                    "frequencies_hz": [round_float(x) for x in frequencies],
                    "heldout_fit_loss": fit["heldout_fit_loss"],
                    "hidden_state_error": fit["recovery"][
                        "canonical_parameter_distance"
                    ],
                }
            )

        transfer_frequencies = TARGET_FREQUENCIES_HZ + SPECTRAL_TRANSFER_OFFSET_HZ
        transfer = run_null_fit(
            n,
            first_seed + 313,
            time,
            args.train_fraction,
            transfer_frequencies,
            TARGET_AMPLITUDES,
            TARGET_PHASES_RAD,
            0.0,
            args.null_steps,
            args,
        )

        reference = base_runs[0]
        learned_f = np.asarray(reference["learned_frequencies_hz"], dtype=float)
        learned_a = np.asarray(reference["learned_amplitudes"], dtype=float)
        learned_p = np.asarray(reference["learned_phases_rad"], dtype=float)
        gauge_shifted = learned_p + 2.0 * np.pi
        reference_wave = build_waveform(time, learned_f, learned_a, learned_p)
        shifted_wave = build_waveform(time, learned_f, learned_a, gauge_shifted)
        gauge_delta = float(np.max(np.abs(reference_wave - shifted_wave)))

        restart_instability = float(np.std(restart_parameters)) if restart_parameters else 0.0
        noise_worst = max(float(item["hidden_state_error"]) for item in noise_results)
        separation_worst = max(
            float(item["hidden_state_error"]) for item in separation_results
        )
        transfer_hidden = float(
            transfer["recovery"]["canonical_parameter_distance"]
        )
        null_fragility = max(noise_worst, separation_worst, transfer_hidden)

        by_count[str(n)] = {
            "restart_count": len(base_runs),
            "restart_heldout_losses": [round_float(x) for x in restart_losses],
            "restart_hidden_state_errors": [round_float(x) for x in restart_parameters],
            "restart_instability": round_float(restart_instability),
            "noise": noise_results,
            "frequency_separation": separation_results,
            "spectral_transfer": {
                "frequencies_hz": [round_float(x) for x in transfer_frequencies],
                "heldout_fit_loss": transfer["heldout_fit_loss"],
                "hidden_state_error": transfer["recovery"][
                    "canonical_parameter_distance"
                ],
            },
            "gauge": {
                "phase_shift_rad": round_float(2.0 * np.pi),
                "max_waveform_delta": round_float(gauge_delta),
                "equivalent_by_declared_phase_periodicity": True,
            },
            "null_fragility": round_float(null_fragility),
            "all_null_results_are_diagnostics": True,
            "global_identifiability_proved": False,
        }

    return {
        "frozen_before_execution": True,
        "restart": {
            "refit_required": True,
            "meaning": "independent seeded optimisation basins",
        },
        "noise": {
            "refit_required": True,
            "levels": NOISE_LEVELS,
            "meaning": "re-estimate under perturbed observation",
        },
        "frequency_separation": {
            "refit_required": True,
            "factors": SEPARATION_FACTORS,
            "meaning": "compress spectral separation and re-estimate",
        },
        "spectral_transfer": {
            "refit_required": True,
            "offset_hz": SPECTRAL_TRANSFER_OFFSET_HZ,
            "meaning": "fit a shifted unseen spectral geometry",
        },
        "gauge": {
            "refit_required": False,
            "semantic_identity_test": True,
            "meaning": "2pi phase relabelling should preserve waveform",
        },
        "by_count": by_count,
    }


def build_eligible_only_pareto(
    runs: list[dict[str, Any]],
    ladder: dict[str, Any],
    args: argparse.Namespace,
) -> dict[str, Any]:
    axes = [
        "model_size",
        "heldout_error",
        "hidden_state_error",
        "restart_instability",
        "null_fragility",
    ]
    models: dict[str, dict[str, Any]] = {}
    heldout_gate = max(0.02, args.observable_tolerance * 10.0)
    hidden_gate = max(0.50, args.parameter_tolerance * 5.0)

    for n in OSCILLATOR_COUNTS:
        selected = [run for run in runs if run["oscillator_count"] == n]
        heldout = float(np.median([run["heldout_fit_loss"] for run in selected]))
        hidden = float(
            np.median(
                [run["recovery"]["canonical_parameter_distance"] for run in selected]
            )
        )
        stress = ladder["by_count"][str(n)]
        restart_instability = float(stress["restart_instability"])
        null_fragility = float(stress["null_fragility"])
        admissible = bool(
            np.isfinite(heldout)
            and np.isfinite(hidden)
            and np.isfinite(restart_instability)
            and np.isfinite(null_fragility)
        )
        consumer_adequate = bool(heldout <= heldout_gate and hidden <= hidden_gate)
        eligible = bool(admissible and consumer_adequate)
        models[str(n)] = {
            "admissible": admissible,
            "consumer_adequate": consumer_adequate,
            "eligible": eligible,
            "pareto_ranked": eligible,
            "costs": {
                "model_size": float(n),
                "heldout_error": round_float(heldout),
                "hidden_state_error": round_float(hidden),
                "restart_instability": round_float(restart_instability),
                "null_fragility": round_float(null_fragility),
            },
        }

    eligible_names = [name for name, model in models.items() if model["eligible"]]
    frontier: list[str] = []
    for name in eligible_names:
        selected = models[name]["costs"]
        dominated = False
        for other_name in eligible_names:
            if other_name == name:
                continue
            other = models[other_name]["costs"]
            weak = all(float(other[axis]) <= float(selected[axis]) for axis in axes)
            strict = any(float(other[axis]) < float(selected[axis]) for axis in axes)
            if weak and strict:
                dominated = True
                break
        if not dominated:
            frontier.append(name)

    return {
        "selection_policy": "admissible_and_consumer_adequate_before_cost_ranking",
        "consumer": "joint_heldout_waveform_and_canonical_hidden_state_recovery",
        "heldout_gate": round_float(heldout_gate),
        "hidden_state_gate": round_float(hidden_gate),
        "axes": axes,
        "models": models,
        "frontier": frontier,
        "lower_cost_implies_truth": False,
        "smaller_n_wins_by_definition": False,
        "larger_n_wins_by_definition": False,
    }


def main() -> int:
    args = parse_args()
    if args.max_steps <= 0 or args.null_steps <= 0 or args.samples < 32 or args.duration <= 0.0:
        raise SystemExit("max-steps, null-steps, samples, and duration must be positive")
    if not 0.0 < args.train_fraction < 1.0:
        raise SystemExit("train-fraction must lie strictly between zero and one")
    if len(args.seeds) < 1:
        raise SystemExit("at least one seed is required")

    time = np.linspace(0.0, args.duration, args.samples, endpoint=False)
    train_time, train_target, heldout_time, heldout_target = split_target(
        time,
        args.train_fraction,
        TARGET_FREQUENCIES_HZ,
        TARGET_AMPLITUDES,
        TARGET_PHASES_RAD,
    )

    runs = [
        optimize(
            n,
            seed,
            train_time,
            train_target,
            heldout_time,
            heldout_target,
            args.max_steps,
            args.learning_rate_amplitude,
            args.learning_rate_phase,
            args.learning_rate_frequency,
            args.observable_tolerance,
            args.parameter_tolerance,
        )
        for n in OSCILLATOR_COUNTS
        for seed in args.seeds
    ]
    near_count = sum(
        int(run["near_collision_diagnostic"]["observed"]) for run in runs
    )
    falsification_ladder = build_falsification_ladder(time, args, runs)
    eligible_only_pareto = build_eligible_only_pareto(
        runs, falsification_ladder, args
    )

    payload: dict[str, Any] = {
        "diagnostic": OUTPUT_STEM,
        "schema_version": 3,
        "status": "synthetic_identifiability_no_promotion",
        "parent_chain": {
            "structural_parent_pr": 896,
            "numerical_parent_pr": 909,
            "parent_following": True,
        },
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
            "null_steps": args.null_steps,
            "learning_rates": {
                "amplitude": args.learning_rate_amplitude,
                "phase": args.learning_rate_phase,
                "frequency": args.learning_rate_frequency,
            },
        },
        "target": {
            "frequencies_hz": [round_float(x) for x in TARGET_FREQUENCIES_HZ],
            "amplitudes": [round_float(x) for x in TARGET_AMPLITUDES],
            "phases_rad": [round_float(x) for x in TARGET_PHASES_RAD],
        },
        "comparison_policy": {
            "same_target_support": True,
            "ranking_required": False,
            "nine_superiority_assumed": False,
            "query_adequacy_is_relative": True,
        },
        "runs": runs,
        "near_collision_summary": {
            "status": "observed" if near_count else "not_observed",
            "count": near_count,
            "run_count": len(runs),
            "exact_nonfactorability_proved": False,
        },
        "falsification_ladder": falsification_ladder,
        "eligible_only_pareto": eligible_only_pareto,
        "promotion": {"state": "blocked", "flags": FAIL_CLOSED_FLAGS},
        "formal_boundary": {
            "numerical_near_collision_is_exact_nonfactorability_proof": False,
            "waveform_adequacy_implies_hidden_state_adequacy": False,
            "optimizer_failure_implies_nonidentifiability": False,
            "null_failure_implies_mechanism_falsity": False,
            "pareto_frontier_implies_truth": False,
        },
    }
    args.out_dir.mkdir(parents=True, exist_ok=True)
    path = args.out_dir / f"{OUTPUT_STEM}.json"
    path.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(payload, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
