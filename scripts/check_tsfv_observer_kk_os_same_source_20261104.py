#!/usr/bin/env python3
"""P01/P02/P07/P08 exact reference: original event access, rational KK
Schur/horizontal metric, and observer-unitary/Euclidean-contract no-go.

This is an independent source-convention test only; it is NOT Agda kernel
acceptance, a continuous Lorentzian metric, physical KK action, OS proof,
or a Yang--Mills Clay theorem. Another worker owns YM R443--R333.
"""
from fractions import Fraction as F
from itertools import product
import random

EVENTS = ("preparation", "intermediate", "terminal")
LEVELS = ("initial", "intermediate", "terminal")
VISIBLE = {
    "initial": (True, False, False),
    "intermediate": (True, True, False),
    "terminal": (True, True, True),
}


def precedes(a, b):
    return all(not ea or eb for ea, eb in zip(VISIBLE[a], VISIBLE[b]))


def check_original_access():
    for a, b, c in product(LEVELS, repeat=3):
        if precedes(a, b) and precedes(b, c):
            assert precedes(a, c)
    assert all(precedes(a, a) for a in LEVELS)
    assert all(
        not (precedes(a, b) and precedes(b, a))
        for a, b in product(LEVELS, repeat=2) if a != b
    )
    for a, b in (("initial", "intermediate"),
                 ("intermediate", "terminal"), ("initial", "terminal")):
        assert precedes(a, b) and not precedes(b, a)
        assert any((not ea) and eb for ea, eb in zip(VISIBLE[a], VISIBLE[b]))
    print("PASS: original 3-level causal-access 27 transitivity cases "
          "and 3 strict event witnesses")


def dot(u, v):
    return sum((x * y for x, y in zip(u, v)), F(0))


def actual_four_bilinear(u, v):
    return -u[0] * v[0] + dot(u[1:], v[1:])


def connection(u):
    return F(1, 3) * u[0] - F(2, 5) * u[2]


def d_lambda(u):
    return -F(5, 7) * u[1] + F(2, 9) * u[3]


def kk_five(g4, gauge_a, r2, u, s, v, t):
    return g4(u, v) + r2 * (s + gauge_a(u)) * (t + gauge_a(v))


def check_kk_horizontal():
    rng = random.Random(2048)
    checked = 0
    for _ in range(8000):
        u = tuple(F(rng.randint(-8, 8), rng.randint(1, 8))
                  for _ in range(4))
        v = tuple(F(rng.randint(-8, 8), rng.randint(1, 8))
                  for _ in range(4))
        s = F(rng.randint(-8, 8), rng.randint(1, 8))
        t = F(rng.randint(-8, 8), rng.randint(1, 8))
        r2 = F(rng.randint(1, 8), rng.randint(1, 8))
        g = actual_four_bilinear
        a = connection
        assert kk_five(g, a, r2, u, -a(u), v, -a(v)) == g(u, v)
        expanded = g(u, v) + r2 * (
            a(u) * a(v) + a(u) * t + s * a(v) + s * t
        )
        assert kk_five(g, a, r2, u, s, v, t) == expanded
        assert kk_five(g, a, r2, u, F(0), v, F(0)) == (
            g(u, v) + r2 * a(u) * a(v)
        )
        shifted = lambda w: a(w) + d_lambda(w)
        assert kk_five(
            g, shifted, r2, u, s - d_lambda(u), v, t - d_lambda(v)
        ) == kk_five(g, a, r2, u, s, v, t)
        assert -(a(u) + d_lambda(u)) == -a(u) - d_lambda(u)
        checked += 5

    timelike = (F(1), F(0), F(0), F(0))
    assert connection(timelike) != 0
    assert kk_five(
        actual_four_bilinear, connection, F(2),
        timelike, F(0), timelike, F(0)
    ) != actual_four_bilinear(timelike, timelike)
    print(f"PASS: {checked:,} exact rational KK horizontal/Schur, "
          "connection/gauge and non-naive-fibre cases")


def check_time_no_go():
    vacuum, positive, negative = "vacuum", "positive", "negative"
    norm = {vacuum: 0, positive: 1, negative: 1}
    real_step = {vacuum: vacuum, positive: negative, negative: positive}
    euclidean_rank_drop = {vacuum: vacuum, positive: vacuum, negative: vacuum}
    for state in (vacuum, positive, negative):
        assert norm[real_step[state]] == norm[state]
    assert norm[euclidean_rank_drop[positive]] < norm[positive]
    assert real_step[positive] != euclidean_rank_drop[positive]
    print("PASS: exact 3-state norm-preserving vs contracting "
          "step-identity negative control (not finite-time OS exponential)")


if __name__ == "__main__":
    check_original_access()
    check_kk_horizontal()
    check_time_no_go()
    print("REFERENCE ONLY: NOT a physical/Agda/Stone/OS/Clay result")
