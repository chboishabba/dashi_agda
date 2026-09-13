#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


OUTPUT_STEM = "continuous_oscillator_synthetic"
OSCILLATOR_COUNTS = [3, 6, 9]
DEFAULT_SEEDS = [7, 17, 29]
TARGET_FREQUENCIES_HZ = np.array([1.0, 2.5, 4.0], dtype=float)
TARGET_AMPLITUDES = np.array([1.0, 0.7, 0.45], dtype=float)
TARGET_PHASES_RAD = np.array([0.2, -0.8, 1.1], dtype=float)
FAIL_CLOSED_FLAGS = {
    "neuroscience_interpretation_promoted": False,
    "memory_mechanism_promoted": False,
    "hebbian_identity_promoted": False,
    "kuramoto_identity_promoted": False,
    "cognitive_dissonance_identity_promoted": False,
    "empirical_brain_fit_promoted": False,
    "three_six_nine_superiority_promoted": False,
    "quantum_interpretation_promoted": False,
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run the bounded synthetic continuous-oscillator diagnostic."
    )
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--seeds", type=int, nargs="+", default=DEFAULT_SEEDS)
    parser.add_argument("--max-steps", type=int, default=1200)
    parser.add_argument("--samples", type=int, default=1024)
    parser.add_argument("--duration", type=float, default=4.0)
    parser.add_argument("--learning-rate-amplitude", type=float, default=0.08)
    parser.add_argument("--learning-rate-phase", type=float, default=0.04)
    parser.add_argument("--lambda-phase", type=float, default=0.002)
    parser.add_argument("--lambda-amplitude", type=float, default=1.0e-5)
    parser.add_argument("--tolerance", type=float, default=1.0e-8)
    parser.add_argument("--snapshot-every", type=int, default=50)
    return parser.parse_args()


def round_float(value: float) -> float:
    return float(round(float(value), 12))


def phase_coherence(phases: np.ndarray) -> float:
    if phases.size == 0:
        return 0.0
    return float(np.abs(np.mean(np.exp(1j * phases))))


def build_target(time: np.ndarray) -> np.ndarray:
    target = np.zeros_like(time)
    for amplitude, frequency, phase in zip(
        TARGET_AMPLITUDES,
        TARGET_FREQUENCIES_HZ,
        TARGET_PHASES_RAD,
    ):
        target += amplitude * np.cos(2.0 * np.pi * frequency * time + phase)
    return target


def frequency_layout(oscillator_count: int) -> tuple[np.ndarray, np.ndarray]:
    repeats = oscillator_count // 3
    frequencies = np.repeat(TARGET_FREQUENCIES_HZ, repeats)
    groups = np.repeat(np.arange(3, dtype=int), repeats)
    return frequencies, groups


def synthesize(
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


def phase_penalty_and_gradient(
    phases: np.ndarray,
    groups: np.ndarray,
) -> tuple[float, np.ndarray]:
    penalty = 0.0
    grad = np.zeros_like(phases)
    pair_count = 0
    for group in range(3):
        idx = np.flatnonzero(groups == group)
        for left_pos in range(len(idx)):
            for right_pos in range(left_pos + 1, len(idx)):
                i = int(idx[left_pos])
                j = int(idx[right_pos])
                delta = phases[i] - phases[j]
                penalty += 1.0 - math.cos(delta)
                s = math.sin(delta)
                grad[i] += s
                grad[j] -= s
                pair_count += 1
    if pair_count:
        penalty /= pair_count
        grad /= pair_count
    return float(penalty), grad


def objective_and_gradient(
    time: np.ndarray,
    target: np.ndarray,
    frequencies: np.ndarray,
    groups: np.ndarray,
    amplitudes: np.ndarray,
    phases: np.ndarray,
    lambda_phase: float,
    lambda_amplitude: float,
) -> tuple[float, float, np.ndarray, np.ndarray, np.ndarray]:
    waveform, cosines, sines = synthesize(
        time,
        frequencies,
        amplitudes,
        phases,
    )
    error = waveform - target
    fit_loss = float(np.mean(error * error))
    phase_penalty, phase_penalty_grad = phase_penalty_and_gradient(phases, groups)
    amplitude_penalty = float(np.mean(amplitudes * amplitudes))
    objective = (
        fit_loss
        + lambda_phase * phase_penalty
        + lambda_amplitude * amplitude_penalty
    )

    grad_amplitudes = 2.0 * np.mean(error[None, :] * cosines, axis=1)
    grad_amplitudes += (
        lambda_amplitude * (2.0 / amplitudes.size) * amplitudes
    )

    grad_phases = 2.0 * np.mean(
        error[None, :] * (-amplitudes[:, None] * sines),
        axis=1,
    )
    grad_phases += lambda_phase * phase_penalty_grad
    return objective, fit_loss, waveform, grad_amplitudes, grad_phases


def serialize_vector(values: np.ndarray) -> list[float]:
    return [round_float(value) for value in values]


def learn_condition(
    oscillator_count: int,
    seed: int,
    time: np.ndarray,
    target: np.ndarray,
    max_steps: int,
    lr_amplitude: float,
    lr_phase: float,
    lambda_phase: float,
    lambda_amplitude: float,
    tolerance: float,
    snapshot_every: int,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    rng = np.random.default_rng(seed + 1000 * oscillator_count)
    frequencies, groups = frequency_layout(oscillator_count)
    repeats = oscillator_count // 3

    base_amplitudes = np.repeat(TARGET_AMPLITUDES / repeats, repeats)
    amplitudes = base_amplitudes * (
        1.0 + rng.normal(0.0, 0.35, size=oscillator_count)
    )
    phases = np.repeat(TARGET_PHASES_RAD, repeats) + rng.normal(
        0.0,
        0.9,
        size=oscillator_count,
    )

    initial_amplitudes = amplitudes.copy()
    initial_phases = phases.copy()
    initial_objective, initial_fit_loss, _, _, _ = objective_and_gradient(
        time,
        target,
        frequencies,
        groups,
        amplitudes,
        phases,
        lambda_phase,
        lambda_amplitude,
    )

    trajectory: list[dict[str, Any]] = []
    last_step_norm = 0.0
    convergence_reason = "max_steps"
    completed_steps = 0

    for step in range(max_steps):
        objective, fit_loss, _waveform, grad_a, grad_phi = objective_and_gradient(
            time,
            target,
            frequencies,
            groups,
            amplitudes,
            phases,
            lambda_phase,
            lambda_amplitude,
        )
        gradient_norm = float(
            np.sqrt(np.sum(grad_a * grad_a) + np.sum(grad_phi * grad_phi))
        )
        if step % snapshot_every == 0:
            trajectory.append(
                {
                    "oscillator_count": oscillator_count,
                    "seed": seed,
                    "step": step,
                    "fit_loss": round_float(fit_loss),
                    "total_objective": round_float(objective),
                    "gradient_norm": round_float(gradient_norm),
                    "global_phase_coherence": round_float(
                        phase_coherence(phases)
                    ),
                }
            )
        if gradient_norm < tolerance:
            convergence_reason = "gradient_tolerance"
            completed_steps = step
            break

        delta_a = -lr_amplitude * grad_a
        delta_phi = -lr_phase * grad_phi
        amplitudes += delta_a
        phases += delta_phi
        phases = (phases + np.pi) % (2.0 * np.pi) - np.pi
        last_step_norm = float(
            np.sqrt(np.sum(delta_a * delta_a) + np.sum(delta_phi * delta_phi))
        )
        completed_steps = step + 1

    (
        final_objective,
        final_fit_loss,
        final_waveform,
        final_grad_a,
        final_grad_phi,
    ) = objective_and_gradient(
        time,
        target,
        frequencies,
        groups,
        amplitudes,
        phases,
        lambda_phase,
        lambda_amplitude,
    )
    final_gradient_norm = float(
        np.sqrt(
            np.sum(final_grad_a * final_grad_a)
            + np.sum(final_grad_phi * final_grad_phi)
        )
    )
    if completed_steps % snapshot_every != 0:
        trajectory.append(
            {
                "oscillator_count": oscillator_count,
                "seed": seed,
                "step": completed_steps,
                "fit_loss": round_float(final_fit_loss),
                "total_objective": round_float(final_objective),
                "gradient_norm": round_float(final_gradient_norm),
                "global_phase_coherence": round_float(phase_coherence(phases)),
            }
        )

    group_coherence = [
        phase_coherence(phases[groups == group]) for group in range(3)
    ]
    correlation = float(np.corrcoef(target, final_waveform)[0, 1])
    loss_reduction_ratio = (
        (initial_fit_loss - final_fit_loss) / initial_fit_loss
        if initial_fit_loss
        else 0.0
    )

    run = {
        "oscillator_count": oscillator_count,
        "seed": seed,
        "frequencies_fixed": True,
        "frequencies_hz": serialize_vector(frequencies),
        "initial_amplitudes": serialize_vector(initial_amplitudes),
        "initial_phases_rad": serialize_vector(initial_phases),
        "final_amplitudes": serialize_vector(amplitudes),
        "final_phases_rad": serialize_vector(phases),
        "initial_fit_loss": round_float(initial_fit_loss),
        "final_fit_loss": round_float(final_fit_loss),
        "initial_total_objective": round_float(initial_objective),
        "final_total_objective": round_float(final_objective),
        "loss_reduction_ratio": round_float(loss_reduction_ratio),
        "waveform_correlation": round_float(correlation),
        "global_phase_coherence": round_float(phase_coherence(phases)),
        "group_phase_coherence": [
            round_float(value) for value in group_coherence
        ],
        "gradient_norm": round_float(final_gradient_norm),
        "parameter_step_norm": round_float(last_step_norm),
        "steps_completed": completed_steps,
        "convergence_reason": convergence_reason,
        "converged": bool(convergence_reason == "gradient_tolerance"),
    }
    return run, trajectory


def aggregate_runs(runs: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    aggregate: dict[str, dict[str, Any]] = {}
    for oscillator_count in OSCILLATOR_COUNTS:
        selected = [
            run for run in runs if run["oscillator_count"] == oscillator_count
        ]
        aggregate[str(oscillator_count)] = {
            "run_count": len(selected),
            "mean_initial_fit_loss": round_float(
                np.mean([run["initial_fit_loss"] for run in selected])
            ),
            "mean_final_fit_loss": round_float(
                np.mean([run["final_fit_loss"] for run in selected])
            ),
            "mean_loss_reduction_ratio": round_float(
                np.mean([run["loss_reduction_ratio"] for run in selected])
            ),
            "mean_waveform_correlation": round_float(
                np.mean([run["waveform_correlation"] for run in selected])
            ),
        }
    return aggregate


def write_csv(
    path: Path,
    fieldnames: list[str],
    rows: list[dict[str, Any]],
) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def build_markdown(payload: dict[str, Any]) -> str:
    lines = [
        "# Continuous oscillator synthetic diagnostic",
        "",
        "Status: `synthetic_only_no_promotion`",
        "",
        (
            "The 3/6/9 conditions share exactly the same three target "
            "frequencies. Larger conditions receive redundant oscillators, "
            "not extra spectral support."
        ),
        "",
        "| N | seed | initial fit | final fit | reduction | correlation |",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    for run in payload["runs"]:
        lines.append(
            f"| {run['oscillator_count']} | {run['seed']} | "
            f"{run['initial_fit_loss']:.6g} | {run['final_fit_loss']:.6g} | "
            f"{run['loss_reduction_ratio']:.6g} | "
            f"{run['waveform_correlation']:.6g} |"
        )
    lines.extend(["", "## Promotion boundary", ""])
    for name, value in payload["promotion"]["flags"].items():
        lines.append(f"- `{name} = {str(value).lower()}`")
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    if (
        args.max_steps <= 0
        or args.samples < 16
        or args.duration <= 0
        or args.snapshot_every <= 0
    ):
        raise SystemExit(
            "max-steps, samples, duration, and snapshot-every must be positive"
        )

    out_dir: Path = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    json_path = out_dir / f"{OUTPUT_STEM}.json"
    trajectories_path = out_dir / "continuous_oscillator_trajectories.csv"
    comparison_path = out_dir / "continuous_oscillator_comparison.csv"
    markdown_path = out_dir / f"{OUTPUT_STEM}.md"

    time = np.linspace(0.0, args.duration, args.samples, endpoint=False)
    target = build_target(time)
    runs: list[dict[str, Any]] = []
    trajectories: list[dict[str, Any]] = []
    for oscillator_count in OSCILLATOR_COUNTS:
        for seed in args.seeds:
            run, trace = learn_condition(
                oscillator_count=oscillator_count,
                seed=seed,
                time=time,
                target=target,
                max_steps=args.max_steps,
                lr_amplitude=args.learning_rate_amplitude,
                lr_phase=args.learning_rate_phase,
                lambda_phase=args.lambda_phase,
                lambda_amplitude=args.lambda_amplitude,
                tolerance=args.tolerance,
                snapshot_every=args.snapshot_every,
            )
            runs.append(run)
            trajectories.extend(trace)

    payload: dict[str, Any] = {
        "diagnostic": OUTPUT_STEM,
        "schema_version": 1,
        "status": "synthetic_only_no_promotion",
        "oscillator_counts": OSCILLATOR_COUNTS,
        "default_seeds": list(args.seeds),
        "target": {
            "frequencies_hz": serialize_vector(TARGET_FREQUENCIES_HZ),
            "amplitudes": serialize_vector(TARGET_AMPLITUDES),
            "phases_rad": serialize_vector(TARGET_PHASES_RAD),
            "duration_seconds": round_float(args.duration),
            "sample_count": args.samples,
        },
        "learning": {
            "max_steps": args.max_steps,
            "learning_rate_amplitude": args.learning_rate_amplitude,
            "learning_rate_phase": args.learning_rate_phase,
            "lambda_phase": args.lambda_phase,
            "lambda_amplitude": args.lambda_amplitude,
            "gradient_tolerance": args.tolerance,
            "frequencies_learned": False,
            "coupling_matrix_learned": False,
        },
        "comparison_policy": {
            "same_frequency_support": True,
            "ranking_required": False,
            "nine_superiority_assumed": False,
        },
        "runs": runs,
        "comparison_by_count": aggregate_runs(runs),
        "promotion": {
            "state": "blocked",
            "flags": FAIL_CLOSED_FLAGS,
        },
        "output_paths": {
            "json": str(json_path),
            "trajectories_csv": str(trajectories_path),
            "comparison_csv": str(comparison_path),
            "markdown": str(markdown_path),
        },
    }

    trajectory_fields = [
        "oscillator_count",
        "seed",
        "step",
        "fit_loss",
        "total_objective",
        "gradient_norm",
        "global_phase_coherence",
    ]
    write_csv(trajectories_path, trajectory_fields, trajectories)
    comparison_fields = [
        "oscillator_count",
        "seed",
        "initial_fit_loss",
        "final_fit_loss",
        "loss_reduction_ratio",
        "waveform_correlation",
        "global_phase_coherence",
        "gradient_norm",
        "parameter_step_norm",
        "steps_completed",
        "convergence_reason",
        "converged",
        "frequencies_fixed",
    ]
    write_csv(
        comparison_path,
        comparison_fields,
        [{key: run[key] for key in comparison_fields} for run in runs],
    )
    markdown_path.write_text(build_markdown(payload), encoding="utf-8")
    json_path.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(payload, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
