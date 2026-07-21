#!/usr/bin/env python3
"""Exact regression for a constant-Jacobian, non-injective polynomial map.

This is an empirical/algebraic diagnostic, not a kernel-level Agda proof.  It
uses exact rational coefficients and a tiny sparse-polynomial implementation,
so it has no third-party dependencies.
"""

from fractions import Fraction
from itertools import permutations

N = 3
ZERO = (0, 0, 0)


def const(c):
    c = Fraction(c)
    return {} if c == 0 else {ZERO: c}


def var(i):
    e = [0] * N
    e[i] = 1
    return {tuple(e): Fraction(1)}


def add(a, b):
    out = dict(a)
    for m, c in b.items():
        out[m] = out.get(m, Fraction(0)) + c
        if out[m] == 0:
            del out[m]
    return out


def neg(a):
    return {m: -c for m, c in a.items()}


def sub(a, b):
    return add(a, neg(b))


def mul(a, b):
    out = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            m = tuple(x + y for x, y in zip(ma, mb))
            out[m] = out.get(m, Fraction(0)) + ca * cb
    return {m: c for m, c in out.items() if c}


def power(a, n):
    out = const(1)
    for _ in range(n):
        out = mul(out, a)
    return out


def scale(c, a):
    return mul(const(c), a)


def diff(a, i):
    out = {}
    for m, c in a.items():
        if m[i]:
            mm = list(m)
            k = mm[i]
            mm[i] -= 1
            out[tuple(mm)] = c * k
    return out


def evaluate(a, point):
    total = Fraction(0)
    for m, c in a.items():
        term = c
        for exponent, value in zip(m, point):
            term *= value ** exponent
        total += term
    return total


def sign(p):
    inversions = sum(p[i] > p[j] for i in range(N) for j in range(i + 1, N))
    return -1 if inversions % 2 else 1


def determinant(matrix):
    out = const(0)
    for p in permutations(range(N)):
        term = const(sign(p))
        for row, col in enumerate(p):
            term = mul(term, matrix[row][col])
        out = add(out, term)
    return out


x, y, z = var(0), var(1), var(2)
one_plus_xy = add(const(1), mul(x, y))
f1 = add(mul(power(one_plus_xy, 3), z), mul(mul(power(y, 2), one_plus_xy), add(const(4), scale(3, mul(x, y)))))
f2 = add(y, add(scale(3, mul(mul(x, power(one_plus_xy, 2)), z)), scale(3, mul(mul(x, power(y, 2)), add(const(4), scale(3, mul(x, y)))))))
f3 = sub(sub(scale(2, x), scale(3, mul(power(x, 2), y))), mul(power(x, 3), z))
F = (f1, f2, f3)
J = [[diff(fi, j) for j in range(N)] for fi in F]
DET = determinant(J)

expected_det = const(-2)
assert DET == expected_det, f"Jacobian determinant mismatch: {DET}"

target = (Fraction(-1, 4), Fraction(0), Fraction(0))
witnesses = (
    (Fraction(0), Fraction(0), Fraction(-1, 4)),
    (Fraction(1), Fraction(-3, 2), Fraction(13, 2)),
    (Fraction(-1), Fraction(3, 2), Fraction(13, 2)),
)

assert len(set(witnesses)) == 3
for point in witnesses:
    image = tuple(evaluate(fi, point) for fi in F)
    assert image == target, f"F{point} = {image}, expected {target}"

print("PASS: det DF = -2 identically")
print("PASS: three distinct exact preimages map to (-1/4, 0, 0)")
