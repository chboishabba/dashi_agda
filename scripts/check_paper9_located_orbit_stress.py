#!/usr/bin/env python3
"""Adversarial exact-rational stress test for Paper 9's located S/T reduction.

This validates the mathematical integer-shift bounds and inversion inequalities.
It does NOT execute or certify the Agda proof term or cover arbitrary Bishop reals.
The T-shift count is computed in closed form, so huge coordinates are testable
without iterating billions of unit translations.
"""
from fractions import Fraction as Q
from math import factorial
import random


def center(x: Q, high_first: bool):
    # This is exactly the first translate used by center in the Agda source.
    n = abs(x).numerator // abs(x).denominator + 1
    z = x + n
    assert abs(x) < n and 0 < z < 2*n

    if high_first:
        # leftFuel stops at x < 2/3; it subtracts while x >= 2/3.
        u = z - Q(2, 3)
        k = max(0, u.numerator // u.denominator + 1)
        assert z-k < Q(2, 3)
    else:
        # Alternate overlapping policy: stop at x <= 1/3.
        u = z - Q(1, 3)
        k = max(0, -((-u.numerator) // u.denominator))
        assert z-k <= Q(1, 3)

    assert 0 <= k <= 2*n
    v = z-k
    assert -Q(2, 3) <= v <= Q(2, 3), (x, v, high_first)
    # The last negative translation is only taken from a point above
    # the relevant threshold, so it cannot cross the lower strip edge.
    if k:
        assert v > -Q(2, 3)
    return v, n, k


def reduce_xy(x: Q, y: Q, high_first: bool):
    assert y > 0
    initial_y = y
    delta = initial_y / 3
    fuel = int(1 / delta) + 1
    inversions = total_t = max_t = 0

    while fuel and (y <= Q(1, 3) if high_first else y < Q(1, 2)):
        assert y >= initial_y
        assert y + fuel*delta >= Q(1, 3)
        x, right, left = center(x, high_first)
        moves = right + left
        assert moves <= 3*right
        total_t += moves
        max_t = max(max_t, moves)

        norm_sq = x*x + y*y
        assert 0 < norm_sq < Q(25, 36) + Q(0, 1)
        assert norm_sq < Q(3, 4)

        old_y = y
        x, y = -x/norm_sq, y/norm_sq
        assert y >= Q(4, 3)*old_y
        assert y >= old_y + delta

        fuel -= 1
        inversions += 1
        assert y + fuel*delta >= Q(1, 3)

    assert y >= Q(1, 3)
    return inversions, total_t, max_t, x, y


def cases():
    # Dense samples immediately around both horizontal strip boundaries
    # and both overlapping height thresholds.
    for den in range(1, 81):
        eps = Q(1, den*1009)
        xs = (
            Q(-2, 3)-eps, Q(-2, 3), Q(-2, 3)+eps,
            Q(-1, 3)-eps, Q(-1, 3), Q(-1, 3)+eps,
            Q(0),
            Q(1, 3)-eps, Q(1, 3), Q(1, 3)+eps,
            Q(2, 3)-eps, Q(2, 3), Q(2, 3)+eps,
        )
        ys = (
            Q(1, 3)-eps, Q(1, 3), Q(1, 3)+eps,
            Q(1, 2)-eps, Q(1, 2), Q(1, 2)+eps,
            Q(1, den*1009),
        )
        for x in xs:
            for y in ys:
                if y > 0:
                    yield x, y

    # Large coordinates and tiny heights expose hidden dependence on
    # bounded integer translation counts.
    rng = random.Random(0x369)
    for _ in range(20_000):
        x = Q(rng.randint(-10**12, 10**12), rng.randint(1, 10**9))
        y = Q(rng.randint(1, 10**9), rng.randint(1, 10**12))
        yield x, y

    for x in (-10**12, -10**9, -1, 0, 1, 10**9, 10**12):
        for y in (Q(1, 10**3), Q(1, 10**6), Q(1, 10**9), Q(1, 10**12)):
            yield Q(x), y


def main():
    inputs = list(cases())
    for high_first in (True, False):
        total = inversions = t_moves = worst = 0
        for x, y in inputs:
            count, moves, maximum, _, _ = reduce_xy(x, y, high_first)
            total += 1
            inversions += count
            t_moves += moves
            worst = max(worst, maximum)
        policy = "high-first" if high_first else "low-first"
        print(f"{policy}: cases={total}, inversions={inversions}, "
              f"unit_T_moves={t_moves}, max_T_moves_per_center={worst}")

    prefix = sum(Q(19, 10)**k/factorial(k) for k in range(5))
    assert prefix == Q(1533881, 240000) > 6
    gap = 6*(Q(1, 3)-Q(1, 64))
    assert gap == Q(61, 32) > Q(19, 10)
    assert Q(25, 36) < Q(3, 4)
    print(f"radius: prefix={prefix}, gap={gap}; exact inequalities PASS")
    print("NOTE: diagnostics only; no Agda/kernel acceptance claimed")


if __name__ == "__main__":
    main()
