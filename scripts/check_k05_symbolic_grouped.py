#!/usr/bin/env python3
"""Exact bivariate Gaussian-rational polynomial regression of the K05 identity.

Finite verification, never an all-N Agda proof. No sampling or floating point.
"""
from fractions import Fraction
from math import comb, factorial
import argparse

ZERO = (Fraction(0), Fraction(0))

def add(a, b):
    return a[0] + b[0], a[1] + b[1]

def push(out, powers, coefficient):
    out[powers] = add(out.get(powers, ZERO), coefficient)

def grouped_convolution(n):
    out = {}
    for k in range(n + 1):
        p = n - k
        xp = Fraction((-1) ** k, factorial(2 * k))
        xq = Fraction((-1) ** k, factorial(2 * k + 1))
        yp = Fraction((-1) ** p, factorial(2 * p))
        yq = Fraction((-1) ** p, factorial(2 * p + 1))
        push(out, (2 * k, 2 * p), (xp * yp, Fraction(0)))
        push(out, (2 * k + 1, 2 * p + 1), (-xq * yq, Fraction(0)))
        push(out, (2 * k, 2 * p + 1), (Fraction(0), xp * yq))
        push(out, (2 * k + 1, 2 * p), (Fraction(0), xq * yp))
    return {k: v for k, v in out.items() if v != ZERO}

def original_at_sum(n):
    out = {}
    for k in range(2 * n + 1):
        push(out, (k, 2 * n - k),
             (Fraction((-1) ** n * comb(2 * n, k), factorial(2 * n)), Fraction(0)))
    for k in range(2 * n + 2):
        push(out, (k, 2 * n + 1 - k),
             (Fraction(0), Fraction((-1) ** n * comb(2 * n + 1, k), factorial(2 * n + 1))))
    return out

def oddodd(n):
    if n < 0:
        return {}
    out = {}
    for k in range(n + 1):
        j = n - k
        coefficient = -Fraction((-1) ** n, factorial(2 * k + 1) * factorial(2 * j + 1))
        push(out, (2 * k + 1, 2 * j + 1), (coefficient, Fraction(0)))
    return out

def verify(n):
    left = grouped_convolution(n)
    right = original_at_sum(n)
    for powers, coefficient in oddodd(n).items():
        push(right, powers, coefficient)
    for powers, coefficient in oddodd(n - 1).items():
        push(right, powers, (-coefficient[0], -coefficient[1]))
    right = {k: v for k, v in right.items() if v != ZERO}
    assert left == right, f"K05 symbolic mismatch at degree {n}: {set(left.items()) ^ set(right.items())}"
    return len(left)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--through-degree", type=int, default=48)
    args = parser.parse_args()
    assert args.through_degree >= 0
    monomials = sum(verify(n) for n in range(args.through_degree + 1))
    print(f"PASS: {args.through_degree + 1} exact bivariate polynomial identities "
          f"(n=0..{args.through_degree}), {monomials} nonzero monomials")
    print("Finite symbolic regression ONLY; universal Agda kernel proof remains open.")
