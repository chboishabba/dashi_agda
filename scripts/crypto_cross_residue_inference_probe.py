#!/usr/bin/env python3
"""Cross-residue CBD→NTT inference probe for the Round-17 blue-team lane.

Primary source:
  National Institute of Standards and Technology,
  "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
  2024. DOI: 10.6028/NIST.FIPS.203.

Purpose
-------
Measure whether the *joint* transported CBD prior across several actual FIPS
quadratic residues gives anomalously cheap conditional recovery compared with a
control that preserves every residue marginal exactly but independently shuffles
residue alignment.

This is a finite defensive/diagnostic experiment. It is not an ML-KEM break and
it does not claim an asymptotic security result.

The probe exposes two complementary experiments:

1. scalar noisy-list geometry on a shared coefficient-source block;
2. actual BaseCaseMultiply conditional-mate geometry on a shared even/odd
   coefficient-source block.

The shuffled control preserves each selected residue marginal and destroys only
cross-residue alignment. Hence a true-vs-shuffled difference isolates dependence
that cannot be explained by single-residue support alone.
"""

from __future__ import annotations

import argparse
import itertools
import random
import statistics
from collections import Counter
from dataclasses import dataclass
from typing import Iterable, Sequence

import numpy as np

Q = 3329
ZETA = 17
CBD2 = (-2, -1, 0, 1, 2)


def bitrev7(i: int) -> int:
    return int(f"{i:07b}"[::-1], 2)


def gamma(i: int) -> int:
    return pow(ZETA, 2 * bitrev7(i) + 1, Q)


def coefficient_states(width: int) -> np.ndarray:
    return np.array(list(itertools.product(CBD2, repeat=width)), dtype=np.int64)


def even_odd_source_states(width: int) -> np.ndarray:
    return np.array(list(itertools.product(CBD2, repeat=2 * width)), dtype=np.int64)


def scalar_joint_image(states: np.ndarray, residues: Sequence[int]) -> np.ndarray:
    width = states.shape[1]
    weights = np.array(
        [[pow(gamma(r), j, Q) for j in range(width)] for r in residues],
        dtype=np.int64,
    )
    return (states @ weights.T) % Q


def quadratic_joint_image(
    source: np.ndarray, width: int, residues: Sequence[int]
) -> np.ndarray:
    even = source[:, :width]
    odd = source[:, width:]
    columns: list[np.ndarray] = []
    for residue in residues:
        g = gamma(residue)
        weights = np.array([pow(g, j, Q) for j in range(width)], dtype=np.int64)
        columns.append((even @ weights) % Q)
        columns.append((odd @ weights) % Q)
    return np.stack(columns, axis=1)


def shuffled_blocks(image: np.ndarray, block_width: int, rng: random.Random) -> np.ndarray:
    """Preserve every residue marginal exactly while destroying alignment."""
    out = image.copy()
    n = len(image)
    block_count = image.shape[1] // block_width
    for block in range(block_count):
        permutation = list(range(n))
        rng.shuffle(permutation)
        lo = block * block_width
        hi = lo + block_width
        out[:, lo:hi] = image[permutation, lo:hi]
    return out


def pack_qary(rows: np.ndarray) -> list[int]:
    packed = np.zeros(len(rows), dtype=object)
    for column in range(rows.shape[1]):
        packed = packed * Q + rows[:, column].astype(object)
    return [int(value) for value in packed]


def image_profile(image: np.ndarray) -> dict[str, float]:
    counts = Counter(pack_qary(image))
    fibres = list(counts.values())
    n = len(image)
    return {
        "states": n,
        "image_size": len(counts),
        "image_fraction": len(counts) / n,
        "max_fibre": max(fibres),
        "mean_fibre_mass": sum(v * v for v in fibres) / n,
        "collision_pairs": sum(v * (v - 1) // 2 for v in fibres),
    }


def noisy_survivor_count(image: np.ndarray, rng: random.Random) -> int:
    """Restricted diagonal noisy-linear residual test over selected residues."""
    support = set(pack_qary(image))
    n, coordinate_count = image.shape
    secret = image[rng.randrange(n)]
    error = image[rng.randrange(n)]
    multipliers = [rng.randrange(1, Q) for _ in range(coordinate_count)]
    target = [
        (multipliers[j] * int(secret[j]) + int(error[j])) % Q
        for j in range(coordinate_count)
    ]
    residual = np.empty_like(image)
    for j in range(coordinate_count):
        residual[:, j] = (target[j] - multipliers[j] * image[:, j]) % Q
    return sum(key in support for key in pack_qary(residual))


def basecase_apply(
    carrier: np.ndarray,
    coefficients: Sequence[tuple[int, int]],
    residues: Sequence[int],
) -> np.ndarray:
    out = np.empty_like(carrier)
    for index, residue in enumerate(residues):
        g = gamma(residue)
        a0, a1 = coefficients[index]
        s0 = carrier[:, 2 * index]
        s1 = carrier[:, 2 * index + 1]
        out[:, 2 * index] = (a0 * s0 + (g * a1 % Q) * s1) % Q
        out[:, 2 * index + 1] = (a1 * s0 + a0 * s1) % Q
    return out


def conditioned_basecase_profile(
    carrier: np.ndarray,
    residues: Sequence[int],
    rng: random.Random,
    left_samples: int,
) -> dict[str, float]:
    """One module row, k=2; condition the first secret polynomial."""
    n = len(carrier)
    true_left_index = rng.randrange(n)
    true_right_index = rng.randrange(n)
    error_index = rng.randrange(n)

    a_left = [(rng.randrange(Q), rng.randrange(Q)) for _ in residues]
    a_right = [(rng.randrange(Q), rng.randrange(Q)) for _ in residues]
    left_map = basecase_apply(carrier, a_left, residues)
    right_map = basecase_apply(carrier, a_right, residues)
    target = (
        left_map[true_left_index]
        + right_map[true_right_index]
        + carrier[error_index]
    ) % Q

    error_support = set(pack_qary(carrier))
    sampled = [rng.randrange(n) for _ in range(max(0, left_samples - 1))]
    sampled.append(true_left_index)

    mate_counts: list[int] = []
    true_left_mates = 0
    for index in sampled:
        residual = (target - left_map[index] - right_map) % Q
        mates = sum(key in error_support for key in pack_qary(residual))
        mate_counts.append(mates)
        if index == true_left_index:
            true_left_mates = mates

    return {
        "mean_mates": statistics.mean(mate_counts),
        "median_mates": statistics.median(mate_counts),
        "max_mates": max(mate_counts),
        "nonempty_fraction": sum(v > 0 for v in mate_counts) / len(mate_counts),
        "functional_fraction": sum(v == 1 for v in mate_counts) / len(mate_counts),
        "true_left_mates": true_left_mates,
    }


def mean(values: Iterable[float]) -> float:
    values = list(values)
    return statistics.mean(values) if values else float("nan")


def scalar_probe(width: int, residues: Sequence[int], repetitions: int, seed: int) -> None:
    source = coefficient_states(width)
    true_joint = scalar_joint_image(source, residues)
    master = random.Random(seed)

    true_counts: list[int] = []
    shuffled_counts: list[int] = []
    shuffled_image_sizes: list[int] = []
    for _ in range(repetitions):
        true_counts.append(noisy_survivor_count(true_joint, random.Random(master.randrange(1 << 30))))
        shuffled = shuffled_blocks(true_joint, 1, random.Random(master.randrange(1 << 30)))
        shuffled_counts.append(noisy_survivor_count(shuffled, random.Random(master.randrange(1 << 30))))
        shuffled_image_sizes.append(int(image_profile(shuffled)["image_size"]))

    profile = image_profile(true_joint)
    print("scalar-cross-residue")
    print(f"  width={width} residues={tuple(residues)} states={len(source)}")
    print(f"  true-image-size={int(profile['image_size'])} fraction={profile['image_fraction']:.6f}")
    print(f"  shuffled-image-size-mean={mean(shuffled_image_sizes):.3f}")
    print(f"  true-survivors-mean={mean(true_counts):.6f}")
    print(f"  shuffled-survivors-mean={mean(shuffled_counts):.6f}")
    print(f"  ratio={mean(true_counts) / mean(shuffled_counts):.6f}")


def basecase_probe(
    width: int,
    residues: Sequence[int],
    repetitions: int,
    left_samples: int,
    seed: int,
) -> None:
    source = even_odd_source_states(width)
    true_joint = quadratic_joint_image(source, width, residues)
    master = random.Random(seed)

    true_profiles: list[dict[str, float]] = []
    shuffled_profiles: list[dict[str, float]] = []
    for _ in range(repetitions):
        true_profiles.append(
            conditioned_basecase_profile(
                true_joint,
                residues,
                random.Random(master.randrange(1 << 30)),
                left_samples,
            )
        )
        shuffled = shuffled_blocks(true_joint, 2, random.Random(master.randrange(1 << 30)))
        shuffled_profiles.append(
            conditioned_basecase_profile(
                shuffled,
                residues,
                random.Random(master.randrange(1 << 30)),
                left_samples,
            )
        )

    print("basecase-cross-residue")
    print(f"  width={width} residues={tuple(residues)} states/poly={len(source)}")
    for key in (
        "mean_mates",
        "median_mates",
        "max_mates",
        "nonempty_fraction",
        "functional_fraction",
        "true_left_mates",
    ):
        print(
            f"  {key}: true={mean(p[key] for p in true_profiles):.6f} "
            f"shuffled={mean(p[key] for p in shuffled_profiles):.6f}"
        )


def parse_residues(text: str) -> tuple[int, ...]:
    result = tuple(int(part.strip()) for part in text.split(",") if part.strip())
    if not result:
        raise argparse.ArgumentTypeError("at least one residue is required")
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=("scalar", "basecase", "both"), default="both")
    parser.add_argument("--width", type=int, default=3)
    parser.add_argument("--residues", type=parse_residues, default=(0, 2))
    parser.add_argument("--repetitions", type=int, default=20)
    parser.add_argument("--left-samples", type=int, default=80)
    parser.add_argument("--seed", type=int, default=20260815)
    args = parser.parse_args()

    if args.mode in ("scalar", "both"):
        scalar_probe(args.width, args.residues, args.repetitions, args.seed)
    if args.mode in ("basecase", "both"):
        basecase_probe(
            args.width,
            args.residues,
            args.repetitions,
            args.left_samples,
            args.seed + 1,
        )


if __name__ == "__main__":
    main()
