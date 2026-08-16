#!/usr/bin/env python3
"""Benchmark exact parity-factorized membership for opposite FIPS NTT residues.

Discovery/defensive research only. This script does not recover ML-KEM keys.
It tests one concrete consequence of the Round-17 opposite-residue theorem:
for evaluation points (a,-a), the CBD coefficient block splits into independent
even/odd source sectors, so the raw transformed error-image membership test can
be represented by two much smaller scalar image sets.

Primary source:
  NIST, Module-Lattice-Based Key-Encapsulation Mechanism Standard, FIPS 203,
  2024. DOI: 10.6028/NIST.FIPS.203.
"""

from __future__ import annotations

import argparse
import random
import statistics
import time
from itertools import product

from crypto_ntt_cbd_block_reconciliation_probe import (
    CBD2,
    GAMMA,
    Q,
    block_signatures_at_points,
)

INV2 = pow(2, -1, Q)


def parity_images(m: int, a: int):
    even_positions = list(range(0, m, 2))
    odd_positions = list(range(1, m, 2))

    even_image = {
        sum(x * pow(a, j, Q) for x, j in zip(coeffs, even_positions)) % Q
        for coeffs in product(CBD2, repeat=len(even_positions))
    }
    odd_image = {
        sum(x * pow(a, j, Q) for x, j in zip(coeffs, odd_positions)) % Q
        for coeffs in product(CBD2, repeat=len(odd_positions))
    }
    return even_image, odd_image


def split_observation(pair: tuple[int, int]):
    plus, minus = pair
    even = ((plus + minus) * INV2) % Q
    odd = ((plus - minus) * INV2) % Q
    return even, odd


def join_sectors(even: int, odd: int):
    return (even + odd) % Q, (even - odd) % Q


def factorized_member(
    pair: tuple[int, int],
    even_image: set[int],
    odd_image: set[int],
):
    even, odd = split_observation(pair)
    return even in even_image and odd in odd_image


def exhaustive_membership_equivalence(m: int, a: int):
    points = (a, (-a) % Q)
    _, signatures = block_signatures_at_points(m, points)
    full_image = set(signatures)
    even_image, odd_image = parity_images(m, a)

    # No false negatives on every source-generated CBD block.
    for signature in signatures:
        assert factorized_member(signature, even_image, odd_image)

    # No false positives: every Cartesian parity-sector pair recombines to a
    # source image point. This is only |E|*|O| checks (271,441 for m=8,a=17),
    # rather than scanning the ambient F_q^2 carrier.
    factorized_image = {
        join_sectors(even, odd)
        for even in even_image
        for odd in odd_image
    }
    assert factorized_image == full_image

    return {
        "source_candidates": len(signatures),
        "full_pair_image": len(full_image),
        "even_image": len(even_image),
        "odd_image": len(odd_image),
        "factorized_scalar_entries": len(even_image) + len(odd_image),
        "factorized_pair_capacity": len(even_image) * len(odd_image),
    }


def conditioned_counts_full_and_factorized(
    m: int,
    a: int,
    trials: int,
    seed: int,
):
    points = (a, (-a) % Q)
    rng = random.Random(seed)
    _, signatures = block_signatures_at_points(m, points)
    full_image = set(signatures)
    even_image, odd_image = parity_images(m, a)
    n = len(signatures)

    instances = []
    for _ in range(trials):
        s = signatures[rng.randrange(n)]
        e0 = signatures[rng.randrange(n)]
        e1 = signatures[rng.randrange(n)]
        alpha0 = [rng.randrange(1, Q), rng.randrange(1, Q)]
        alpha1 = [rng.randrange(1, Q), rng.randrange(1, Q)]
        r0 = tuple(
            (points[j] * alpha1[j] * s[j] + e0[j]) % Q for j in range(2)
        )
        r1 = tuple((alpha0[j] * s[j] + e1[j]) % Q for j in range(2))
        instances.append((alpha0, alpha1, r0, r1))

    def enumerate_with(member):
        values = []
        start = time.perf_counter()
        for alpha0, alpha1, r0, r1 in instances:
            survivors = 0
            for candidate in signatures:
                need0 = (
                    (r0[0] - points[0] * alpha1[0] * candidate[0]) % Q,
                    (r0[1] - points[1] * alpha1[1] * candidate[1]) % Q,
                )
                if not member(need0):
                    continue
                need1 = (
                    (r1[0] - alpha0[0] * candidate[0]) % Q,
                    (r1[1] - alpha0[1] * candidate[1]) % Q,
                )
                if member(need1):
                    survivors += 1
            values.append(survivors)
        return values, time.perf_counter() - start

    full_values, full_seconds = enumerate_with(full_image.__contains__)
    fact_values, fact_seconds = enumerate_with(
        lambda pair: factorized_member(pair, even_image, odd_image)
    )
    assert full_values == fact_values

    return {
        "survivor_mean": statistics.mean(full_values),
        "survivor_min": min(full_values),
        "survivor_max": max(full_values),
        "full_seconds": full_seconds,
        "factorized_seconds": fact_seconds,
        "time_ratio_factorized_over_full": factorized_seconds / full_seconds,
        "full_pair_image_entries": len(full_image),
        "factorized_scalar_entries": len(even_image) + len(odd_image),
        "entry_reduction_ratio":
            len(full_image) / (len(even_image) + len(odd_image)),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--m", type=int, default=8)
    parser.add_argument("--trials", type=int, default=6)
    args = parser.parse_args()

    assert (GAMMA[0] + GAMMA[1]) % Q == 0
    assert (GAMMA[2] + GAMMA[3]) % Q == 0

    for a in (GAMMA[0], GAMMA[2]):
        print(f"opposite evaluation pair a={a}, -a={(-a) % Q}, m={args.m}")
        profile = exhaustive_membership_equivalence(args.m, a)
        print("exact membership profile", profile)
        conditioned = conditioned_counts_full_and_factorized(
            args.m,
            a,
            args.trials,
            seed=2026081530 + args.m + a,
        )
        print("conditioned enumeration benchmark", conditioned)

    print("\nInterpretation boundary:")
    print("  * membership equivalence is exact for the finite CBD block image tested")
    print("  * the main immediate win is representation size/cache footprint")
    print("  * Python wall-clock timing is diagnostic, not an implementation lower bound")
    print("  * candidate enumeration remains O(5^m) in this script")


if __name__ == "__main__":
    main()
