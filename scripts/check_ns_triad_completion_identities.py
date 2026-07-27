#!/usr/bin/env python3
"""Exact integer checks for the Stage-3 algebraic completion tranche.

This is a finite regression oracle, not a finite-to-uniform proof. It checks
literal shell consequences, resonant null identities and the three-leg orbit
over all nonzero cutoff-cube triads at the requested cutoff.
"""

from __future__ import annotations

import argparse
from itertools import product
from typing import Iterator, Tuple

Mode = Tuple[int, int, int]


def add(a: Mode, b: Mode) -> Mode:
    return tuple(x + y for x, y in zip(a, b))  # type: ignore[return-value]


def neg(a: Mode) -> Mode:
    return (-a[0], -a[1], -a[2])


def dot(a: Mode, b: Mode) -> int:
    return sum(x * y for x, y in zip(a, b))


def cross(a: Mode, b: Mode) -> Mode:
    return (
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    )


def inf_norm(a: Mode) -> int:
    return max(abs(x) for x in a)


def shell(a: Mode) -> int:
    magnitude = inf_norm(a)
    if magnitude <= 1:
        return 0
    return (magnitude - 1).bit_length()


def modes(cutoff: int) -> list[Mode]:
    return [
        k
        for k in product(range(-cutoff, cutoff + 1), repeat=3)
        if k != (0, 0, 0)
    ]


def triads(cutoff: int) -> Iterator[tuple[Mode, Mode, Mode]]:
    lattice = modes(cutoff)
    present = set(lattice)
    for p in lattice:
        for q in lattice:
            k = add(p, q)
            if k in present:
                yield p, q, k


def transverse_samples(k: Mode) -> tuple[Mode, Mode]:
    axes: tuple[Mode, ...] = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
    axis = min(axes, key=lambda candidate: abs(dot(k, candidate)))
    first = cross(k, axis)
    if first == (0, 0, 0):
        raise AssertionError(("degenerate axis", k, axis))
    second = cross(k, first)
    if second == (0, 0, 0):
        raise AssertionError(("degenerate second frame", k, first))
    assert dot(k, first) == 0
    assert dot(k, second) == 0
    return first, second


def verify(cutoff: int, separation: int) -> dict[str, int]:
    count = 0
    low_high = 0
    high_low = 0
    high_high_low = 0

    for p, q, k in triads(cutoff):
        count += 1
        assert add(p, q) == k

        assert add(k, neg(q)) == p
        assert add(k, neg(p)) == q

        for u_p in transverse_samples(p):
            assert dot(u_p, q) == dot(u_p, k)
        for u_q in transverse_samples(q):
            assert dot(u_q, p) == dot(u_q, k)

        jp, jq, jk = shell(p), shell(q), shell(k)
        if jp + separation <= jq:
            low_high += 1
            assert abs(jk - jq) <= 1, (p, q, k, jp, jq, jk)
        if jq + separation <= jp:
            high_low += 1
            assert abs(jk - jp) <= 1, (p, q, k, jp, jq, jk)
        if jk + separation <= jp and jk + separation <= jq:
            high_high_low += 1
            assert abs(jp - jq) <= 1, (p, q, k, jp, jq, jk)

    return {
        "cutoff": cutoff,
        "triads": count,
        "low_high": low_high,
        "high_low": high_low,
        "high_high_low": high_high_low,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cutoff", type=int, default=3)
    parser.add_argument("--separation", type=int, default=3)
    args = parser.parse_args()
    if args.cutoff < 1:
        raise SystemExit("--cutoff must be positive")
    result = verify(args.cutoff, args.separation)
    print(" ".join(f"{key}={value}" for key, value in result.items()))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
