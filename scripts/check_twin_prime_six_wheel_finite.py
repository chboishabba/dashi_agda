#!/usr/bin/env python3
"""Independent exact-integer regression for DASHI's {2,3} twin-offset sieve.

This checks finite residue arithmetic and bounded examples only. It is not
an Agda kernel check, a Maynard sieve proof, or evidence for infinitely many
twin primes. Classical sieve roots: Eratosthenes, Brun; finite DASHI donors:
SixWheelSieveCountExact and SixWheelCRTExact.
"""
from __future__ import annotations

from math import gcd, isqrt


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    return all(n % d for d in range(2, isqrt(n) + 1))


def survives_pair_mod6(n: int) -> bool:
    return gcd(n, 6) == 1 and gcd(n + 2, 6) == 1


def check() -> None:
    # These six literal cases match the Agda CRT classifications.
    assert [r for r in range(6) if survives_pair_mod6(r)] == [5]
    assert [((r + 2) % 6) for r in range(6)] == [2, 3, 4, 5, 0, 1]

    for blocks in (1, 2, 10, 127, 1000):
        survivors = [n for n in range(6 * blocks) if survives_pair_mod6(n)]
        assert survivors == [6 * k + 5 for k in range(blocks)]
        assert len(survivors) == blocks

    # The residue sieve is necessary, not sufficient: 35 is composite.
    assert survives_pair_mod6(35) and not is_prime(35)
    assert is_prime(37)

    twin_pairs = [n for n in range(4, 100001) if is_prime(n) and is_prime(n + 2)]
    assert twin_pairs and all(n % 6 == 5 for n in twin_pairs)
    assert 5 in twin_pairs and 11 in twin_pairs
    print(f"finite wheel: 6/6 residue cases, five repeated block sizes; "
          f"{len(twin_pairs)} bounded twin pairs checked; non-sufficiency witness 35")
    print("status: exact finite computational check; no unbounded-prime result")


if __name__ == "__main__":
    check()
