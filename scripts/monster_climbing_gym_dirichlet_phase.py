#!/usr/bin/env python3
"""Multiplicative Dirichlet-phase diagnostics for the Monster climbing-gym lane.

This producer deliberately separates three layers:

1. the finite observable already used in the phase-control tranche,
      p^(i gamma) = exp(i gamma log p);
2. per-prime means and the full pair kernel
      K[p,q] = mean_gamma (p/q)^(i gamma);
3. a *diagnostic* subtraction of the leading fixed-X Landau term.

For a critical-line zero rho = 1/2 + i gamma, Landau's fixed-X main term

    sum_{0 < gamma <= T} X^rho ~ -(T / 2pi) Lambda(X)

suggests, for a prime p,

    mean p^(i gamma) ~ -(DeltaT / (2pi N)) log(p)/sqrt(p)

over a height window of span DeltaT.  This script subtracts only that leading
prime-sensitive term.  It does not claim that the resulting finite-window
residual is an exact explicit formula, a theorem proof, or a confirmatory
Monster statistic.

The discovery window is zeros 1..849.  A disjoint held-out window 850..1698 is
carried separately and uses DeltaT = gamma_1698 - gamma_849, not gamma_1698.
That distinction is essential when differencing the cumulative Landau main term.
"""
from __future__ import annotations

import argparse
import cmath
import itertools
import json
import math
from pathlib import Path
from typing import Sequence

OGG_PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71)
NON_OGG_CONTROLS = (37, 43, 53, 61, 67)
ALL_PRIMES = OGG_PRIMES + NON_OGG_CONTROLS
ACTUAL_CONTROL_INDICES = tuple(range(len(OGG_PRIMES), len(ALL_PRIMES)))
BALANCED_ASSIGNMENT_COUNT = math.comb(len(ALL_PRIMES), len(NON_OGG_CONTROLS))


def load_zero_cache(path: Path) -> list[float]:
    """Decode one positive, strictly increasing delta-coded zero window."""
    payload = json.loads(path.read_text())
    scale = int(payload["scale"])
    encoded = [int(x) for x in payload["first_plus_deltas"]]
    declared_count = int(payload.get("count", len(encoded)))
    if scale <= 0 or declared_count != len(encoded) or not encoded:
        raise ValueError("invalid zero-cache scale/count")
    values: list[float] = []
    current = 0
    for index, value in enumerate(encoded):
        current = value if index == 0 else current + value
        values.append(current / scale)
    if any(x <= 0.0 for x in values):
        raise ValueError("zero ordinates must be positive")
    if any(a >= b for a, b in zip(values, values[1:])):
        raise ValueError("zero ordinates must be strictly increasing")
    return values


def _complex_record(z: complex) -> dict[str, float]:
    return {"re": float(z.real), "im": float(z.imag), "abs": float(abs(z))}


def landau_prime_mean_main(prime: int, height_span: float, sample_count: int) -> float:
    """Leading fixed-prime Landau main term for the mean p^(i gamma).

    This is a source-shaped diagnostic normalization, not an asserted exact
    finite-window formula.  ``height_span`` is the difference of the upper and
    lower cumulative cutoffs for the selected window.
    """
    if sample_count <= 0 or height_span < 0.0:
        raise ValueError("sample_count must be positive and height_span nonnegative")
    return -(height_span / (2.0 * math.pi * sample_count)) * math.log(prime) / math.sqrt(prime)


def _phase_vectors(zeros: Sequence[float]) -> list[list[complex]]:
    return [
        [cmath.exp(1j * t * math.log(p)) for t in zeros]
        for p in ALL_PRIMES
    ]


def _moments_from_vectors(vectors: Sequence[Sequence[complex]]) -> tuple[list[complex], list[list[complex]]]:
    if not vectors or not vectors[0]:
        raise ValueError("phase vectors must be nonempty")
    n = len(vectors[0])
    if any(len(v) != n for v in vectors):
        raise ValueError("phase vectors must have equal length")
    means = [sum(v) / n for v in vectors]
    gram: list[list[complex]] = []
    for vi in vectors:
        row: list[complex] = []
        for vj in vectors:
            row.append(sum(a * b.conjugate() for a, b in zip(vi, vj)) / n)
        gram.append(row)
    return means, gram


def _residualize_vectors(
    vectors: Sequence[Sequence[complex]],
    height_span: float,
) -> tuple[list[list[complex]], list[float]]:
    n = len(vectors[0])
    main = [landau_prime_mean_main(p, height_span, n) for p in ALL_PRIMES]
    residual = [
        [z - main_i for z in row]
        for row, main_i in zip(vectors, main)
    ]
    return residual, main


def _partition_statistics(
    means: Sequence[complex],
    gram: Sequence[Sequence[complex]],
    selected: Sequence[int],
) -> tuple[float, float]:
    """Return mean |C|^2 and |mean C| for one balanced control assignment."""
    m = len(ALL_PRIMES)
    base_energy = sum(gram[i][j].real for i in range(m) for j in range(m))
    column_real_sums = [sum(gram[i][j].real for i in range(m)) for j in range(m)]
    base_mean = sum(means)
    energy = (
        base_energy
        - 8.0 * sum(column_real_sums[j] for j in selected)
        + 16.0 * sum(gram[j][k].real for j in selected for k in selected)
    )
    mean_vector = base_mean - 4.0 * sum(means[j] for j in selected)
    return float(energy), float(abs(mean_vector))


def _exhaustive_balanced_control(
    means: Sequence[complex],
    gram: Sequence[Sequence[complex]],
) -> dict[str, float | int]:
    actual_energy, actual_coherence = _partition_statistics(
        means, gram, ACTUAL_CONTROL_INDICES
    )
    assignment_count = 0
    energy_le = energy_ge = coherence_le = coherence_ge = 0
    energy_min = math.inf
    energy_max = -math.inf
    coherence_min = math.inf
    coherence_max = -math.inf
    for selected in itertools.combinations(
        range(len(ALL_PRIMES)), len(NON_OGG_CONTROLS)
    ):
        energy, coherence = _partition_statistics(means, gram, selected)
        assignment_count += 1
        energy_le += energy <= actual_energy
        energy_ge += energy >= actual_energy
        coherence_le += coherence <= actual_coherence
        coherence_ge += coherence >= actual_coherence
        energy_min = min(energy_min, energy)
        energy_max = max(energy_max, energy)
        coherence_min = min(coherence_min, coherence)
        coherence_max = max(coherence_max, coherence)
    if assignment_count != BALANCED_ASSIGNMENT_COUNT:
        raise AssertionError("balanced partition enumeration is incomplete")
    return {
        "actual_mean_energy": actual_energy,
        "energy_lower_or_equal_count": energy_le,
        "energy_upper_or_equal_count": energy_ge,
        "energy_lower_tail_fraction": energy_le / assignment_count,
        "energy_upper_tail_fraction": energy_ge / assignment_count,
        "energy_min": energy_min,
        "energy_max": energy_max,
        "actual_mean_vector_magnitude": actual_coherence,
        "coherence_lower_or_equal_count": coherence_le,
        "coherence_upper_or_equal_count": coherence_ge,
        "coherence_lower_tail_fraction": coherence_le / assignment_count,
        "coherence_upper_tail_fraction": coherence_ge / assignment_count,
        "coherence_min": coherence_min,
        "coherence_max": coherence_max,
        "assignment_count": assignment_count,
    }


def analyse_window(
    zeros: Sequence[float],
    *,
    window_label: str,
    lower_height: float = 0.0,
) -> dict[str, object]:
    """Analyse one fixed zero window with raw and Landau-main residual statistics."""
    if not zeros:
        raise ValueError("zero window must be nonempty")
    if lower_height < 0.0 or lower_height >= zeros[0]:
        raise ValueError("lower_height must precede the first zero in the window")
    vectors = _phase_vectors(zeros)
    means, gram = _moments_from_vectors(vectors)
    height_span = float(zeros[-1] - lower_height)
    residual_vectors, main = _residualize_vectors(vectors, height_span)
    residual_means, residual_gram = _moments_from_vectors(residual_vectors)

    prime_moments = []
    for index, prime in enumerate(ALL_PRIMES):
        prime_moments.append(
            {
                "prime": prime,
                "class": "Ogg15" if index < len(OGG_PRIMES) else "nonOgg5-control",
                "raw_mean": _complex_record(means[index]),
                "landau_prime_mean_main": main[index],
                "residual_mean": _complex_record(residual_means[index]),
                "actual_contrast_coefficient": 1 if index < len(OGG_PRIMES) else -3,
                "actual_raw_mean_contribution": _complex_record(
                    means[index] * (1 if index < len(OGG_PRIMES) else -3)
                ),
                "actual_residual_mean_contribution": _complex_record(
                    residual_means[index] * (1 if index < len(OGG_PRIMES) else -3)
                ),
            }
        )

    pair_kernel = [
        [_complex_record(gram[i][j]) for j in range(len(ALL_PRIMES))]
        for i in range(len(ALL_PRIMES))
    ]
    residual_pair_kernel = [
        [_complex_record(residual_gram[i][j]) for j in range(len(ALL_PRIMES))]
        for i in range(len(ALL_PRIMES))
    ]

    return {
        "contract": "monster_climbing_gym_dirichlet_phase_window",
        "window_label": window_label,
        "zero_count": len(zeros),
        "lower_height": float(lower_height),
        "upper_height": float(zeros[-1]),
        "height_span": height_span,
        "ogg_count": len(OGG_PRIMES),
        "control_count": len(NON_OGG_CONTROLS),
        "combined_prime_count": len(ALL_PRIMES),
        "balanced_assignment_count": BALANCED_ASSIGNMENT_COUNT,
        "raw": _exhaustive_balanced_control(means, gram),
        "landau_prime_main_residual": _exhaustive_balanced_control(
            residual_means, residual_gram
        ),
        "prime_moments": prime_moments,
        "pair_kernel": pair_kernel,
        "residual_pair_kernel": residual_pair_kernel,
        "landau_main_term_claimed_exact_finite_formula": False,
        "randomization_hypothesis_established": False,
        "combinatorial_percentile_reported": True,
        "confirmatory_p_value_claimed": False,
        "multiple_statistic_warning": True,
        "replicated_monster_specific_anomaly_claimed": False,
        "riemann_hypothesis_evidence_claimed": False,
    }


def analyse_discovery_and_held_out(
    discovery: Sequence[float], held_out: Sequence[float]
) -> dict[str, object]:
    """Run the locked discovery/held-out pair with the correct cumulative span."""
    if discovery[-1] >= held_out[0]:
        raise ValueError("held-out zero window must be strictly above discovery")
    return {
        "contract": "monster_climbing_gym_dirichlet_phase_maxcut",
        "discovery": analyse_window(
            discovery, window_label="zeros-1-849", lower_height=0.0
        ),
        "held_out": analyse_window(
            held_out,
            window_label="zeros-850-1698",
            lower_height=float(discovery[-1]),
        ),
        "held_out_window_disjoint": True,
        "held_out_statistic_changed_after_inspection": False,
        "held_out_raw_coherence_replicates_discovery_tail": False,
        "held_out_landau_residual_replicates_discovery_tail": False,
        "monster_specificity_promoted": False,
        "formal_promotion": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--discovery-json", type=Path, required=True)
    parser.add_argument("--held-out-json", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = analyse_discovery_and_held_out(
        load_zero_cache(args.discovery_json), load_zero_cache(args.held_out_json)
    )
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
