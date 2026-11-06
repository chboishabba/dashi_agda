#!/usr/bin/env python3
"""Exact rational Q[i] regression for the source all-degree Cayley equation.

This is a non-promotional test. Agda proves the symbolic all-degree formula;
the script tests independently the first N coefficients of
(1-iX)F(X) = 1+iX, where F(0)=1, F_1=2i,
and F_(n+2)=i F_(n+1). It does NOT prove Bishop atan/exp evaluation.
"""

import argparse
from fractions import Fraction as F


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def neg(a):
    return (-a[0], -a[1])


def mul(a, b):
    return (a[0] * b[0] - a[1] * b[1],
            a[0] * b[1] + a[1] * b[0])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--through-degree", type=int, default=4095)
    args = parser.parse_args()
    if args.through_degree < 2 or args.through_degree > 100000:
        raise SystemExit("Degree must lie between 2 and 100000")
    z, one, imag, two_imag = (F(0), F(0)), (F(1), F(0)), (F(0), F(1)), (F(0), F(2))
    prior = None
    current = one
    for n in range(args.through_degree + 1):
        if n == 0:
            current = one
            cross = one
        elif n == 1:
            prior, current = one, two_imag
            cross = add(current, neg(mul(imag, prior)))
        else:
            prior, current = current, mul(imag, current)
            cross = add(current, neg(mul(imag, prior)))
        expected = one if n == 0 else imag if n == 1 else z
        if cross != expected:
            raise AssertionError(f"degree={n}: {cross} != {expected}")
    print(f"PASS: {args.through_degree+1} exact Q[i] Cayley denominator coefficients")
    print("Symbolic Agda uniqueness and native Bishop analytic equality are independent obligations.")


if __name__ == "__main__":
    main()
