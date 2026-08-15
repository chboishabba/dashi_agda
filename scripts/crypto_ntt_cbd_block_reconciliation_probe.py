#!/usr/bin/env python3
"""Source-faithful finite probe for ML-KEM/FIPS-203 CBD block reconciliation.

This is a discovery script, not an attack implementation and not a security claim.
It studies a conditioned local model already exposed by the Round-17 Agda work:
all coefficients outside one parity-block slice are assumed known/removed, and we
ask how many CBD2 secret-block candidates survive a small number of actual FIPS
NTT residue equations when two independent CBD2 error blocks are marginalized.

Primary source:
  NIST, Module-Lattice-Based Key-Encapsulation Mechanism Standard, FIPS 203,
  2024. DOI: 10.6028/NIST.FIPS.203.

The important structural comparison is between opposite FIPS residues such as
(0,1), where gamma_1 = -gamma_0, and generic residue pairs. Opposite residues
split a coefficient block into even/odd sectors. The probe now includes seeded
random field-point controls so that an apparent list-size improvement is not
mistaken for a generic two-equation effect.
"""

from __future__ import annotations

import argparse
import random
import statistics
from collections import Counter
from itertools import product

Q = 3329
ZETA = 17
CBD2 = range(-2, 3)


def bitrev7(i: int) -> int:
    return int(f"{i:07b}"[::-1], 2)


def gamma(i: int) -> int:
    return pow(ZETA, 2 * bitrev7(i) + 1, Q)


GAMMA = [gamma(i) for i in range(128)]


def block_signatures_at_points(m: int, points: tuple[int, ...]):
    weights = [[pow(a, j, Q) for j in range(m)] for a in points]
    candidates = list(product(CBD2, repeat=m))
    signatures = [
        tuple(sum(x * w for x, w in zip(candidate, row)) % Q for row in weights)
        for candidate in candidates
    ]
    return candidates, signatures


def block_signatures(m: int, residues: tuple[int, ...]):
    return block_signatures_at_points(m, tuple(GAMMA[i] for i in residues))


def raw_profile(m: int, residues: tuple[int, ...]):
    _, signatures = block_signatures(m, residues)
    counts = Counter(signatures)
    n = len(signatures)
    collision_pairs = sum(c * (c - 1) // 2 for c in counts.values())
    conditional_mass = sum(c * c for c in counts.values())
    return {
        "candidates": n,
        "images": len(counts),
        "collision_pairs": collision_pairs,
        "conditional_mass": conditional_mass,
        "mean_list": conditional_mass / n,
        "max_fibre": max(counts.values()),
    }


def conditioned_mate_lists_at_points(
    m: int,
    points: tuple[int, ...],
    trials: int,
    seed: int,
):
    """Conditioned BaseCase-style finite block model.

    At evaluation point a_j we use

      R0_j = a_j * alpha1_j * S_j + E0_j
      R1_j =       alpha0_j * S_j + E1_j,

    with known random nonzero alpha0_j,alpha1_j. S,E0,E1 are transforms of
    independent CBD2 m-coefficient blocks. For each generated observation we
    enumerate only S candidates and test whether required E0/E1 signatures lie
    in the exact finite error image. Runtime is O(5^m), not O(5^(3m)).
    """
    rng = random.Random(seed)
    _, signatures = block_signatures_at_points(m, points)
    image = set(signatures)
    n = len(signatures)
    result = []

    for _ in range(trials):
        s = signatures[rng.randrange(n)]
        e0 = signatures[rng.randrange(n)]
        e1 = signatures[rng.randrange(n)]
        alpha0 = [rng.randrange(1, Q) for _ in points]
        alpha1 = [rng.randrange(1, Q) for _ in points]

        r0 = tuple(
            (points[j] * alpha1[j] * s[j] + e0[j]) % Q
            for j in range(len(points))
        )
        r1 = tuple(
            (alpha0[j] * s[j] + e1[j]) % Q
            for j in range(len(points))
        )

        survivors = 0
        for candidate in signatures:
            need0 = tuple(
                (r0[j] - points[j] * alpha1[j] * candidate[j]) % Q
                for j in range(len(points))
            )
            if need0 not in image:
                continue
            need1 = tuple(
                (r1[j] - alpha0[j] * candidate[j]) % Q
                for j in range(len(points))
            )
            if need1 in image:
                survivors += 1
        result.append(survivors)
    return result


def conditioned_mate_lists(
    m: int,
    residues: tuple[int, ...],
    trials: int,
    seed: int,
):
    return conditioned_mate_lists_at_points(
        m,
        tuple(GAMMA[i] for i in residues),
        trials,
        seed,
    )


def summarize(values):
    return {
        "mean": statistics.mean(values),
        "stdev": statistics.pstdev(values),
        "min": min(values),
        "max": max(values),
    }


def random_field_pairs(count: int, seed: int):
    rng = random.Random(seed)
    pairs = []
    while len(pairs) < count:
        left = rng.randrange(1, Q)
        right = rng.randrange(1, Q)
        if left == right or (left + right) % Q == 0:
            continue
        pairs.append((left, right))
    return pairs


def benchmark_opposite_vs_random(m: int, trials: int, baseline_pairs: int):
    opposite = ((GAMMA[0], GAMMA[1]), (GAMMA[2], GAMMA[3]))
    controls = random_field_pairs(baseline_pairs, 2026081500 + m)

    opposite_means = []
    print(f"\nseeded opposite-vs-random benchmark m={m}")
    for index, points in enumerate(opposite):
        values = conditioned_mate_lists_at_points(
            m, points, trials, 2026081510 + 100 * m + index
        )
        summary = summarize(values)
        opposite_means.append(summary["mean"])
        print(f"opposite points={points} {summary}")

    control_means = []
    for index, points in enumerate(controls):
        values = conditioned_mate_lists_at_points(
            m, points, trials, 2026081520 + 100 * m + index
        )
        summary = summarize(values)
        control_means.append(summary["mean"])
        print(f"control  points={points} {summary}")

    opposite_mean = statistics.mean(opposite_means)
    control_mean = statistics.mean(control_means)
    ratio = opposite_mean / control_mean
    print(
        "benchmark aggregate",
        {
            "opposite_mean": opposite_mean,
            "random_control_mean": control_mean,
            "opposite/control": ratio,
            "control_median": statistics.median(control_means),
        },
    )
    return ratio


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--trials", type=int, default=12)
    parser.add_argument("--max-block", type=int, default=8)
    parser.add_argument("--baseline-pairs", type=int, default=6)
    parser.add_argument(
        "--include-m9",
        action="store_true",
        help="also benchmark m=9 (5^9 candidates; materially heavier memory/runtime)",
    )
    args = parser.parse_args()

    assert Q == 3329
    assert GAMMA[0] == 17
    assert GAMMA[1] == 3312
    assert (GAMMA[0] + GAMMA[1]) % Q == 0
    assert GAMMA[2] == 2761
    assert GAMMA[3] == 568
    assert (GAMMA[2] + GAMMA[3]) % Q == 0

    # Durable exact raw regressions discovered in the larger-block pass.
    p01 = raw_profile(8, (0, 1))
    p02 = raw_profile(8, (0, 2))
    p03 = raw_profile(8, (0, 3))
    assert p01 == {
        "candidates": 390625,
        "images": 271441,
        "collision_pairs": 151632,
        "conditional_mass": 693889,
        "mean_list": 693889 / 390625,
        "max_fibre": 4,
    }
    assert p02["collision_pairs"] == 20805
    assert p02["images"] == 369865
    assert p03["collision_pairs"] == 0
    assert p03["images"] == 390625

    print("FIPS constants: gamma0=17, gamma1=-17, gamma2=2761, gamma3=-2761")
    print("raw m=8 profiles:")
    for residues, profile in [((0, 1), p01), ((0, 2), p02), ((0, 3), p03)]:
        print(residues, profile)

    print("\nconditioned BaseCase-style secret-list sizes")
    pairs = ((0, 1), (0, 2), (0, 3), (2, 3))
    for m in range(4, args.max_block + 1):
        for residues in pairs:
            values = conditioned_mate_lists(
                m,
                residues,
                trials=args.trials,
                seed=20260815 + 100 * m + 10 * residues[0] + residues[1],
            )
            print(f"m={m} residues={residues} {summarize(values)}")

    # This is the primary falsification control. At m=8 the opposite FIPS pairs
    # reproducibly leave substantially smaller conditioned lists than seeded
    # generic field-point pairs; m=9 checks whether the separation persists.
    benchmark_opposite_vs_random(8, args.trials, args.baseline_pairs)
    if args.include_m9:
        benchmark_opposite_vs_random(9, max(3, args.trials // 4), args.baseline_pairs)

    print("\nInterpretation boundary:")
    print("  * This is a conditioned slice: coefficients outside the block are assumed removed.")
    print("  * A small local list is not a whole-key attack or runtime claim.")
    print("  * Opposite residue pairs are algebraically special; random controls test whether that matters.")
    print("  * Promote only reproducible structural anomalies to Agda theorems.")


if __name__ == "__main__":
    main()
