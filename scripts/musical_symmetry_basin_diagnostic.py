#!/usr/bin/env python3
"""Honest finite/Monte-Carlo diagnostic for musical-symmetry dynamics.

This script separates three claims:

1. Exact finite witness: a two-bit melody repair has symmetric fixed points and
   two equal basins of volume two.
2. Geometric null: nearest-prototype assignment has no built-in symmetry
   preference.
3. Compression hypothesis: a shorter grammar code for reverse-inversion
   symmetric prototypes can enlarge their assigned basin share.

The third item is a candidate mechanism, not a cognitive result.  The script
therefore always reports ``cognitive_explanation_promoted = False``.
"""

from __future__ import annotations

import argparse
import json
import math
import random
import statistics
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence

PITCH_CLASSES = 12
Melody = tuple[int, ...]


@dataclass(frozen=True)
class Prototype:
    name: str
    melody: Melody
    symmetric: bool


def circular_distance(a: int, b: int) -> int:
    delta = abs(a - b) % PITCH_CLASSES
    return min(delta, PITCH_CLASSES - delta)


def melody_distance(left: Sequence[int], right: Sequence[int]) -> int:
    if len(left) != len(right):
        raise ValueError("melodies must have the same length")
    return sum(circular_distance(a, b) for a, b in zip(left, right, strict=True))


def transpose(melody: Sequence[int], amount: int) -> Melody:
    return tuple((pitch + amount) % PITCH_CLASSES for pitch in melody)


def canonical_transposition(melody: Sequence[int]) -> Melody:
    if not melody:
        raise ValueError("melody must be non-empty")
    return transpose(melody, -int(melody[0]))


def reverse_inversion(melody: Sequence[int], axis: int) -> Melody:
    return tuple((axis - pitch) % PITCH_CLASSES for pitch in reversed(melody))


def reverse_inversion_defect(melody: Sequence[int]) -> int:
    """Minimum distance to a reverse-inversion transform over all T/I axes."""
    return min(
        melody_distance(melody, reverse_inversion(melody, axis))
        for axis in range(PITCH_CLASSES)
    )


def generate_symmetric_melody(length: int, rng: random.Random) -> Melody:
    if length <= 0 or length % 2 != 0:
        raise ValueError("the demonstration uses a positive even melody length")
    axis = rng.randrange(PITCH_CLASSES)
    melody = [0] * length
    for index in range(length // 2):
        pitch = rng.randrange(PITCH_CLASSES)
        melody[index] = pitch
        melody[length - 1 - index] = (axis - pitch) % PITCH_CLASSES
    result = canonical_transposition(melody)
    if reverse_inversion_defect(result) != 0:
        raise AssertionError("symmetric generator failed")
    return result


def generate_generic_melody(length: int, rng: random.Random) -> Melody:
    while True:
        melody = canonical_transposition(
            tuple(rng.randrange(PITCH_CLASSES) for _ in range(length))
        )
        if reverse_inversion_defect(melody) > 0:
            return melody


def make_prototypes(
    length: int,
    symmetric_count: int,
    generic_count: int,
    rng: random.Random,
) -> list[Prototype]:
    if symmetric_count <= 0 or generic_count <= 0:
        raise ValueError("both prototype classes must be non-empty")

    prototypes: list[Prototype] = []
    seen: set[Melody] = set()

    for index in range(symmetric_count):
        melody = generate_symmetric_melody(length, rng)
        while melody in seen:
            melody = generate_symmetric_melody(length, rng)
        seen.add(melody)
        prototypes.append(Prototype(f"sym-{index + 1}", melody, True))

    for index in range(generic_count):
        melody = generate_generic_melody(length, rng)
        while melody in seen:
            melody = generate_generic_melody(length, rng)
        seen.add(melody)
        prototypes.append(Prototype(f"gen-{index + 1}", melody, False))

    return prototypes


def grammar_code_length(prototype: Prototype) -> int:
    """Symbol-count proxy for a simple reverse-inversion grammar.

    A symmetric sequence stores half of the pitches plus one axis symbol.
    A generic sequence stores all pitches.  This is an MDL hypothesis, not a
    perceptual law.
    """
    length = len(prototype.melody)
    return length // 2 + 1 if prototype.symmetric else length


def assign_prototype(
    melody: Melody,
    prototypes: Sequence[Prototype],
    compression_weight: float,
    code_lengths: Sequence[int] | None = None,
) -> int:
    if not prototypes:
        raise ValueError("at least one prototype is required")
    if code_lengths is None:
        code_lengths = [grammar_code_length(prototype) for prototype in prototypes]
    if len(code_lengths) != len(prototypes):
        raise ValueError("code-length vector must match prototype count")

    scores = [
        melody_distance(melody, prototype.melody)
        + compression_weight * code_length
        for prototype, code_length in zip(prototypes, code_lengths, strict=True)
    ]
    return min(range(len(scores)), key=lambda index: (scores[index], index))


def basin_share(
    prototypes: Sequence[Prototype],
    sample_count: int,
    rng: random.Random,
    compression_weight: float,
    shuffled_code_control: bool = False,
) -> float:
    code_lengths = [grammar_code_length(prototype) for prototype in prototypes]
    if shuffled_code_control:
        rng.shuffle(code_lengths)

    symmetric_assignments = 0
    length = len(prototypes[0].melody)
    for _ in range(sample_count):
        melody = canonical_transposition(
            tuple(rng.randrange(PITCH_CLASSES) for _ in range(length))
        )
        winner = assign_prototype(
            melody,
            prototypes,
            compression_weight,
            code_lengths,
        )
        symmetric_assignments += int(prototypes[winner].symmetric)
    return symmetric_assignments / sample_count


def percentile(values: Sequence[float], probability: float) -> float:
    if not values:
        raise ValueError("cannot compute a percentile of an empty sample")
    ordered = sorted(values)
    position = probability * (len(ordered) - 1)
    low = math.floor(position)
    high = math.ceil(position)
    if low == high:
        return ordered[low]
    weight = position - low
    return ordered[low] * (1.0 - weight) + ordered[high] * weight


def summarize(values: Sequence[float]) -> dict[str, float]:
    return {
        "mean": statistics.fmean(values),
        "minimum": min(values),
        "maximum": max(values),
        "q025": percentile(values, 0.025),
        "q975": percentile(values, 0.975),
    }


def exact_two_bit_witness() -> dict[str, object]:
    states = ((0, 0), (0, 1), (1, 0), (1, 1))

    def repair(state: tuple[int, int]) -> tuple[int, int]:
        return (state[0], state[0])

    basins = {(0, 0): 0, (1, 1): 0}
    for state in states:
        repaired = repair(state)
        if repaired not in basins:
            raise AssertionError("repair did not land in the symmetric fixed set")
        basins[repaired] += 1

    return {
        "state_count": len(states),
        "fixed_points": [[0, 0], [1, 1]],
        "basin_volumes": {"00": basins[(0, 0)], "11": basins[(1, 1)]},
        "all_repaired_states_are_symmetric": all(
            repair(state)[0] == repair(state)[1] for state in states
        ),
        "repair_is_idempotent": all(
            repair(repair(state)) == repair(state) for state in states
        ),
    }


def run_experiment(
    *,
    length: int = 8,
    symmetric_count: int = 3,
    generic_count: int = 3,
    sample_count: int = 2_000,
    trials: int = 12,
    compression_weight: float = 1.0,
    seed: int = 20260719,
) -> dict[str, object]:
    if sample_count <= 0 or trials <= 0:
        raise ValueError("sample_count and trials must be positive")

    geometric_null: list[float] = []
    compression_hypothesis: list[float] = []
    shuffled_code_control: list[float] = []

    for trial in range(trials):
        prototype_rng = random.Random(seed + 10_000 * trial)
        prototypes = make_prototypes(
            length,
            symmetric_count,
            generic_count,
            prototype_rng,
        )

        geometric_null.append(
            basin_share(
                prototypes,
                sample_count,
                random.Random(seed + 10_000 * trial + 1),
                compression_weight=0.0,
            )
        )
        compression_hypothesis.append(
            basin_share(
                prototypes,
                sample_count,
                random.Random(seed + 10_000 * trial + 2),
                compression_weight=compression_weight,
            )
        )
        shuffled_code_control.append(
            basin_share(
                prototypes,
                sample_count,
                random.Random(seed + 10_000 * trial + 3),
                compression_weight=compression_weight,
                shuffled_code_control=True,
            )
        )

    return {
        "model": {
            "carrier": f"(Z/{PITCH_CLASSES}Z)^{length} modulo global transposition",
            "symmetry": "reverse-inversion fixed class, minimized over T/I axis",
            "distance": "sum of circular pitch-class distances",
            "compression_code": "half-sequence plus axis for symmetric prototypes; full sequence otherwise",
        },
        "parameters": {
            "length": length,
            "symmetric_prototypes": symmetric_count,
            "generic_prototypes": generic_count,
            "sample_count_per_trial": sample_count,
            "trials": trials,
            "compression_weight": compression_weight,
            "seed": seed,
        },
        "exact_finite_witness": exact_two_bit_witness(),
        "symmetric_basin_share": {
            "geometric_null": summarize(geometric_null),
            "compression_hypothesis": summarize(compression_hypothesis),
            "shuffled_code_control": summarize(shuffled_code_control),
        },
        "claim_boundary": {
            "algebraic_dynamical_extension_demonstrated": True,
            "direct_asymmetry_reward_used": False,
            "compression_prior_assumed": True,
            "null_model_comparison_present": True,
            "human_perception_data_present": False,
            "cross_corpus_replication_present": False,
            "cognitive_explanation_promoted": False,
        },
    }


def write_svg(report: dict[str, object], path: Path) -> None:
    shares = report["symmetric_basin_share"]
    labels = [
        ("Geometric null", shares["geometric_null"]["mean"]),
        ("MDL hypothesis", shares["compression_hypothesis"]["mean"]),
        ("Shuffled-code control", shares["shuffled_code_control"]["mean"]),
    ]

    width, height = 900, 520
    chart_left, chart_top, chart_width, chart_height = 120, 150, 680, 250
    bar_width = 130
    gap = 90

    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        '<rect width="100%" height="100%" fill="white"/>',
        '<text x="450" y="45" text-anchor="middle" font-family="sans-serif" font-size="26" font-weight="bold">Musical symmetry basin diagnostic</text>',
        '<text x="450" y="78" text-anchor="middle" font-family="sans-serif" font-size="15">Null geometry vs compression hypothesis; no cognitive promotion</text>',
        f'<line x1="{chart_left}" y1="{chart_top + chart_height}" x2="{chart_left + chart_width}" y2="{chart_top + chart_height}" stroke="black"/>',
        f'<line x1="{chart_left}" y1="{chart_top}" x2="{chart_left}" y2="{chart_top + chart_height}" stroke="black"/>',
    ]

    for tick in range(6):
        value = tick / 5
        y = chart_top + chart_height * (1 - value)
        parts.append(
            f'<line x1="{chart_left - 5}" y1="{y:.1f}" x2="{chart_left + chart_width}" y2="{y:.1f}" stroke="#dddddd"/>'
        )
        parts.append(
            f'<text x="{chart_left - 12}" y="{y + 5:.1f}" text-anchor="end" font-family="sans-serif" font-size="12">{value:.1f}</text>'
        )

    for index, (label, value) in enumerate(labels):
        x = chart_left + 70 + index * (bar_width + gap)
        bar_height = chart_height * value
        y = chart_top + chart_height - bar_height
        parts.extend(
            [
                f'<rect x="{x}" y="{y:.1f}" width="{bar_width}" height="{bar_height:.1f}" fill="#7a7a7a"/>',
                f'<text x="{x + bar_width / 2}" y="{y - 8:.1f}" text-anchor="middle" font-family="sans-serif" font-size="14">{value:.3f}</text>',
                f'<text x="{x + bar_width / 2}" y="{chart_top + chart_height + 30}" text-anchor="middle" font-family="sans-serif" font-size="13">{label}</text>',
            ]
        )

    parts.extend(
        [
            '<text x="28" y="285" transform="rotate(-90 28 285)" text-anchor="middle" font-family="sans-serif" font-size="14">Symmetric basin share</text>',
            '<text x="450" y="485" text-anchor="middle" font-family="sans-serif" font-size="13">A larger MDL basin is evidence for the assumed compression prior, not yet evidence about human cognition.</text>',
            '</svg>',
        ]
    )
    path.write_text("\n".join(parts), encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--length", type=int, default=8)
    parser.add_argument("--symmetric-prototypes", type=int, default=3)
    parser.add_argument("--generic-prototypes", type=int, default=3)
    parser.add_argument("--samples", type=int, default=2_000)
    parser.add_argument("--trials", type=int, default=12)
    parser.add_argument("--compression-weight", type=float, default=1.0)
    parser.add_argument("--seed", type=int, default=20260719)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-svg", type=Path)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    report = run_experiment(
        length=args.length,
        symmetric_count=args.symmetric_prototypes,
        generic_count=args.generic_prototypes,
        sample_count=args.samples,
        trials=args.trials,
        compression_weight=args.compression_weight,
        seed=args.seed,
    )
    rendered = json.dumps(report, indent=2, sort_keys=True)
    print(rendered)
    if args.output_json is not None:
        args.output_json.write_text(rendered + "\n", encoding="utf-8")
    if args.output_svg is not None:
        write_svg(report, args.output_svg)


if __name__ == "__main__":
    main()
