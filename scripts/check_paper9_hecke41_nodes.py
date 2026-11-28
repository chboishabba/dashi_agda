#!/usr/bin/env python3
"""Exact 43-node signed polynomial uniqueness preflight, not analytic Hecke proof."""
from fractions import Fraction
from math import factorial
from random import Random

D = 42
SIGNED = tuple(range(-21, 22))
UNSIGNED = tuple(range(43))

def evaluate(coeffs, x):
    a = 0
    for c in reversed(coeffs):
        a = a * x + c
    return a

def differences(values):
    v = list(map(Fraction, values))
    ans = []
    while v:
        ans.append(v[0])
        v = [v[i + 1] - v[i] for i in range(len(v) - 1)]
    return ans

def reconstruct(values, origin):
    assert len(values) == 43
    result = [Fraction(0)] * 43
    basis = [Fraction(1)]
    for k, delta in enumerate(differences(values)):
        for i, b in enumerate(basis):
            result[i] += delta * b
        if k < D:
            nxt = [Fraction(0)] * (len(basis) + 1)
            for i, b in enumerate(basis):
                nxt[i] -= (origin + k) * b / (k + 1)
                nxt[i + 1] += b / (k + 1)
            basis = nxt
    return result

def run():
    rng = Random(16341)
    cases = 0
    for nodes in (SIGNED, UNSIGNED):
        for coeffs in (
            [0] * 42 + [1],
            [(-1)**i * (i + 1) for i in range(43)],
            [rng.randrange(-10000, 10000) for _ in range(43)]
        ):
            values = [evaluate(coeffs, y) for y in nodes]
            assert reconstruct(values, nodes[0]) == list(map(Fraction, coeffs))
            assert evaluate(reconstruct(values, nodes[0]), -640320**3) == evaluate(coeffs, -640320**3)
            cases += 1
    assert reconstruct([0] * 43, -21) == [Fraction(0)] * 43
    cases += 1
    corrupt = [0] * 43
    corrupt[21] = 1
    assert any(reconstruct(corrupt, -21))
    cases += 1
    # Negative control: degree 43 defeats 43-node uniqueness.
    extra = [1]
    for y in SIGNED:
        nxt = [0] * (len(extra) + 1)
        for i, c in enumerate(extra):
            nxt[i] -= y * c
            nxt[i + 1] += c
        extra = nxt
    assert extra[-1] == 1 and all(evaluate(extra, y) == 0 for y in SIGNED)
    assert evaluate(extra, 22) == factorial(43)
    cases += 1
    even = [3, -7, 4] + [0] * 19
    odd = [2, 5, -1] + [0] * 18
    c = [0] * 43
    for i, x in enumerate(even): c[2*i] = x
    for i, x in enumerate(odd): c[2*i+1] = x
    for y in SIGNED:
        assert evaluate(c, y) + evaluate(c, -y) == 2 * evaluate(even, y*y)
        assert evaluate(c, y) - evaluate(c, -y) == 2 * y * evaluate(odd, y*y)
    cases += 1
    det = 1
    for k in range(1, 43): det *= factorial(k)
    assert det != 0
    print(f"PAPER9_HECKE41_43_NODE_PREFLIGHT_OK cases={cases} degree=42 determinant_digits={len(str(det))}")
    print("SCOPE: finite polynomial uniqueness only; not global Hecke rigidity or kernel proof")

if __name__ == "__main__":
    run()
