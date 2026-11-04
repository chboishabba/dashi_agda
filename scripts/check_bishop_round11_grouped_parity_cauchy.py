#!/usr/bin/env python3
"""Exact finite audit of the K05 Round11 mixed Cauchy parity boundary.

The actual Round11 cosine/sine series group even and odd Taylor degrees:
  a_n(x) = (i*x)^n/n!
  b_n(x) = a_{2n}(x) + a_{2n+1}(x)
  O_n(x,y) = sum_{k=0}^n a_{2k+1}(x)*a_{2(n-k)+1}(y).

The universal target (NOT proved by this finite script) is
  sum_{k=0}^n b_k(x)*b_{n-k}(y)
    = b_n(x+y) + O_n(x,y) - O_{n-1}(x,y), O_{-1}=0.

The telescope then gives a single O_N boundary rather than a new
uncontrolled generic parity regrouping. All calculations below use
exact Fraction arithmetic; there are no float tolerances.

This is a finite regression, not a substitute for the Agda --safe
all-n proof or the Bishop limit O_N -> 0.
Attribution: Cauchy's product, original DASHI Bishop/Round11 owners,
Bishop--Bridges, Murray/Csimma and the Lean #104 factorial mirror.
"""
from fractions import Fraction
from itertools import product
from math import factorial

ZERO = (Fraction(0), Fraction(0))
SAMPLES = (
    Fraction(0), Fraction(1, 5), Fraction(1, 239),
    Fraction(-2, 7), Fraction(3, 2),
)


def plus(a, b):
    return (a[0] + b[0], a[1] + b[1])


def minus(a, b):
    return (a[0] - b[0], a[1] - b[1])


def times(a, b):
    return (a[0] * b[0] - a[1] * b[1],
            a[0] * b[1] + a[1] * b[0])


def a(n, x):
    q = x ** n / factorial(n)
    return ((q, Fraction(0)), (Fraction(0), q),
            (-q, Fraction(0)), (Fraction(0), -q))[n % 4]


def b(n, x):
    return plus(a(2 * n, x), a(2 * n + 1, x))


def odd_odd(n, x, y):
    if n < 0:
        return ZERO
    out = ZERO
    for k in range(n + 1):
        out = plus(out, times(a(2 * k + 1, x), a(2 * (n - k) + 1, y)))
    return out


def check():
    checked = 0
    for x, y in product(SAMPLES, repeat=2):
        running_row = ZERO
        running_b = ZERO
        for n in range(20):
            row = ZERO
            for k in range(n + 1):
                row = plus(row, times(b(k, x), b(n - k, y)))
            expected = plus(
                minus(b(n, x + y), odd_odd(n - 1, x, y)),
                odd_odd(n, x, y))
            assert row == expected, (x, y, n, row, expected)
            # Independently verify the actual telescoped N-stage equation.
            running_row = plus(running_row, row)
            running_b = plus(running_b, b(n, x + y))
            assert running_row == plus(running_b, odd_odd(n, x, y))
            checked += 1
    return checked


if __name__ == "__main__":
    print("PASS:", check(),
          "exact K05 grouped parity and telescoping cases")
