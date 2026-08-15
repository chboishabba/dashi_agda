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
(0,1), where gamma_1 = -gamma_0, and generic residue pairs.  Opposite residues
split an 8-coefficient parity slice into even/odd subproblems.  The probe checks
whether that algebraic split changes conditional candidate-list geometry.
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


def block_signatures(m: int, residues: tuple[int, ...]):
    weights = [[pow(GAMMA[i], j, Q) for j in range(m)] for i in residues]
    points = list(product(CBD2, repeat=m))
    signatures = [
        tuple(sum(x * w for x, w in zip(point, row)) % Q for row in weights)
        for point in points
    ]
    return points, signatures


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


def conditioned_mate_lists(
    m: int,
    residues: tuple[int, ...],
    trials: int,
    seed: int,
):
    """Conditioned BaseCase-style finite block model.

    For each selected residue i we use

      R0_i = gamma_i * a1_i * S_i + E0_i
      R1_i =             a0_i * S_i + E1_i,

    with known random nonzero a0_i,a1_i.  S,E0,E1 are transforms of independent
    CBD2 m-coefficient blocks.  For each generated observation we enumerate only
    S candidates and test whether the required E0/E1 signatures remain in the
    exact finite error image.  Thus runtime is O(5^m), not O(5^(3m)).
    """
    rng = random.Random(seed)
    _, signatures = block_signatures(m, residues)
    image = set(signatures)
    n = len(signatures)
    result = []

    for _ in range(trials):
        s_idx = rng.randrange(n)
        e0_idx = rng.randrange(n)
        e1_idx = rng.randrange(n)
        s = signatures[s_idx]
        e0 = signatures[e0_idx]
        e1 = signatures[e1_idx]
        a0 = [rng.randrange(1, Q) for _ in residues]
        a1 = [rng.randrange(1, Q) for _ in residues]

        r0 = tuple(
            (GAMMA[residue] * a1[j] * s[j] + e0[j]) % Q
            for j, residue in enumerate(residues)
        )
        r1 = tuple((a0[j] * s[j] + e1[j]) % Q for j in range(len(residues)))

        survivors = 0
        for candidate in signatures:
            need0 = tuple(
                (r0[j] - GAMMA[residue] * a1[j] * candidate[j]) % Q
                for j, residue in enumerate(residues)
            )
            if need0 not in image:
                continue
            need1 = tuple(
                (r1[j] - a0[j] * candidate[j]) % Q
                for j in range(len(residues))
            )
            if need1 in image:
                survivors += 1
        result.append(survivors)
    return result


def summarize(values):
    return {
        "mean": statistics.mean(values),
        "stdev": statistics.pstdev(values),
        "min": min(values),
        "max": max(values),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--trials", type=int, default=12)
    parser.add_argument("--max-block", type=int, default=8)
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

    print("\nInterpretation boundary:")
    print("  * This is a conditioned slice: coefficients outside the block are assumed removed.")
    print("  * A small local list is not a whole-key attack or runtime claim.")
    print("  * Opposite residue pairs are algebraically special; compare them against generic pairs.")
    print("  * Promote only reproducible structural anomalies to Agda theorems.")


if __name__ == "__main__":
    main()
