#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import numpy as np

OUTPUT_STEM = "continuous_oscillator_update_law_discrimination"
OSCILLATOR_COUNTS = [3, 6, 9]
DEFAULT_SEEDS = [7, 17, 29]
TARGET_FREQUENCIES_HZ = np.array([1.0, 2.5, 4.0], dtype=float)
TARGET_AMPLITUDES = np.array([1.0, 0.7, 0.45], dtype=float)
TARGET_PHASES_RAD = np.array([0.2, -0.8, 1.1], dtype=float)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compare local oscillator update vector fields without promoting mechanism identity."
    )
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--seeds", type=int, nargs="+", default=DEFAULT_SEEDS)
    parser.add_argument("--samples", type=int, default=512)
    parser.add_argument("--duration", type=float, default=4.0)
    parser.add_argument("--kuramoto-k", type=float, default=1.0)
    return parser.parse_args()


def round_float(value: float) -> float:
    return float(round(float(value), 12))


def target_waveform(time: np.ndarray) -> np.ndarray:
    args = (
        2.0 * np.pi * TARGET_FREQUENCIES_HZ[:, None] * time[None, :]
        + TARGET_PHASES_RAD[:, None]
    )
    return np.sum(TARGET_AMPLITUDES[:, None] * np.cos(args), axis=0)


def initial_state(n: int, seed: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    repeats = n // 3
    rng = np.random.default_rng(seed + 1000 * n)
    frequencies = np.repeat(TARGET_FREQUENCIES_HZ, repeats)
    amplitudes = np.repeat(TARGET_AMPLITUDES / repeats, repeats)
    phases = np.repeat(TARGET_PHASES_RAD, repeats)
    amplitudes = amplitudes * (1.0 + rng.normal(0.0, 0.25, size=n))
    phases = phases + rng.normal(0.0, 0.55, size=n)
    return frequencies, amplitudes, phases


def local_fields(
    time: np.ndarray,
    target: np.ndarray,
    frequencies: np.ndarray,
    amplitudes: np.ndarray,
    phases: np.ndarray,
    kuramoto_k: float,
) -> dict[str, np.ndarray]:
    args = 2.0 * np.pi * frequencies[:, None] * time[None, :] + phases[:, None]
    x = np.cos(args)
    s = np.sin(args)
    y = np.sum(amplitudes[:, None] * x, axis=0)
    error = y - target

    # Negative gradient of mean squared reconstruction error.
    current_amplitude = -2.0 * np.mean(error[None, :] * x, axis=1)
    current_phase = 2.0 * np.mean(
        error[None, :] * amplitudes[:, None] * s,
        axis=1,
    )

    # A modern correlation-style rule often called "Hebbian" in modelling.
    # The exact equation is NOT attributed to Hebb's 1949 book by this runtime.
    hebbian_style_amplitude = np.mean(y[None, :] * x, axis=1)

    # Oja's normalized linear-neuron rule on the same amplitude coordinates:
    # dw_i = E[y x_i - y^2 w_i].
    oja_amplitude = np.mean(
        y[None, :] * x - (y[None, :] ** 2) * amplitudes[:, None],
        axis=1,
    )

    # Kuramoto phase coupling on the shared phase coordinates, deliberately
    # excluding the target-driven reconstruction term of the current gradient.
    delta = phases[None, :] - phases[:, None]
    kuramoto_phase = (kuramoto_k / phases.size) * np.sum(np.sin(delta), axis=1)

    return {
        "current_amplitude": current_amplitude,
        "current_phase": current_phase,
        "hebbian_style_amplitude": hebbian_style_amplitude,
        "oja_amplitude": oja_amplitude,
        "kuramoto_phase": kuramoto_phase,
    }


def compare_vectors(current: np.ndarray, candidate: np.ndarray) -> dict[str, Any]:
    current_norm = float(np.linalg.norm(current))
    candidate_norm = float(np.linalg.norm(candidate))
    if current_norm <= 1.0e-15 or candidate_norm <= 1.0e-15:
        cosine = 0.0
    else:
        cosine = float(np.dot(current, candidate) / (current_norm * candidate_norm))
        cosine = max(-1.0, min(1.0, cosine))

    denom = float(np.dot(candidate, candidate))
    scale = float(np.dot(current, candidate) / denom) if denom > 1.0e-30 else 0.0
    residual = current - scale * candidate
    if current_norm > 1.0e-15:
        residual_ratio = float(np.linalg.norm(residual) / current_norm)
    else:
        residual_ratio = 0.0

    return {
        "cosine_similarity": round_float(cosine),
        "best_scalar": round_float(scale),
        "best_scaled_residual_ratio": round_float(residual_ratio),
        "current_norm": round_float(current_norm),
        "candidate_norm": round_float(candidate_norm),
        "exact_reduction_proved": False,
        "empirical_mechanism_identity_proved": False,
    }


def compare_run(n: int, seed: int, time: np.ndarray, target: np.ndarray, k: float) -> dict[str, Any]:
    frequencies, amplitudes, phases = initial_state(n, seed)
    fields = local_fields(time, target, frequencies, amplitudes, phases, k)

    hebbian = compare_vectors(
        fields["current_amplitude"], fields["hebbian_style_amplitude"]
    )
    hebbian["coordinate"] = "amplitude"
    hebbian["source_equation_claim"] = "modern_hebbian_style_correlation_candidate_not_direct_hebb_1949_equation"

    oja = compare_vectors(fields["current_amplitude"], fields["oja_amplitude"])
    oja["coordinate"] = "amplitude"
    oja["source_equation_claim"] = "oja_linear_normalized_update_on_shared_amplitude_coordinates"

    kuramoto = compare_vectors(fields["current_phase"], fields["kuramoto_phase"])
    kuramoto["coordinate"] = "phase"
    kuramoto["source_equation_claim"] = "kuramoto_phase_coupling_without_target_error_drive"

    return {
        "oscillator_count": n,
        "seed": seed,
        "comparisons": {
            "hebbian_style_correlation": hebbian,
            "oja": oja,
            "kuramoto": kuramoto,
        },
        "frequency_coordinate_compared": False,
        "same_state_variables_paid": {
            "hebbian_style_correlation": True,
            "oja": True,
            "kuramoto": True,
        },
        "same_full_update_equation_paid": {
            "hebbian_style_correlation": False,
            "oja": False,
            "kuramoto": False,
        },
    }


def main() -> int:
    args = parse_args()
    if args.samples < 32 or args.duration <= 0.0:
        raise SystemExit("samples and duration must be positive")
    if len(args.seeds) < 1:
        raise SystemExit("at least one seed is required")

    time = np.linspace(0.0, args.duration, args.samples, endpoint=False)
    target = target_waveform(time)
    runs = [
        compare_run(n, seed, time, target, args.kuramoto_k)
        for n in OSCILLATOR_COUNTS
        for seed in args.seeds
    ]

    payload: dict[str, Any] = {
        "diagnostic": OUTPUT_STEM,
        "schema_version": 1,
        "status": "synthetic_comparator_no_identity_promotion",
        "parent_chain": {
            "structural_parent_pr": 896,
            "numerical_parent_pr": 909,
            "identifiability_parent": "ContinuousOscillatorIdentifiabilityReceipt",
            "source_boundary_parent": "ContinuousOscillatorUpdateLawAttributionExact",
        },
        "oscillator_counts": OSCILLATOR_COUNTS,
        "candidates": [
            "current_gradient",
            "hebbian_style_correlation",
            "oja",
            "kuramoto",
        ],
        "source_roles": {
            "hebb": {
                "source": "Donald O. Hebb, The Organization of Behavior, Wiley, 1949",
                "doi": None,
                "exact_equation_attributed": False,
                "role": "historical synaptic-learning precedent",
            },
            "oja": {
                "source": "Erkki Oja, A simplified neuron model as a principal component analyzer, 1982",
                "doi": "10.1007/BF00275687",
                "exact_equation_attributed": True,
                "role": "normalized linear learning-rule comparator",
            },
            "kuramoto": {
                "source": "Yoshiki Kuramoto, Chemical Oscillations, Waves, and Turbulence, 1984",
                "doi": "10.1007/978-3-642-69689-3",
                "exact_equation_attributed": True,
                "role": "coupled phase-oscillator comparator",
            },
        },
        "comparison_policy": {
            "shared_coordinate_required": True,
            "best_scalar_projection_is_local_diagnostic": True,
            "local_vector_similarity_is_global_reduction": False,
            "similarity_creates_mechanism_identity": False,
            "frequency_coordinate_coercion_allowed": False,
        },
        "runs": runs,
        "promotion": {
            "gradient_equals_hebbian": False,
            "gradient_equals_oja": False,
            "gradient_equals_kuramoto": False,
            "neural_mechanism_identity": False,
            "biological_phase_locking_identity": False,
            "three_six_nine_superiority": False,
        },
    }

    args.out_dir.mkdir(parents=True, exist_ok=True)
    path = args.out_dir / f"{OUTPUT_STEM}.json"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(payload, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
