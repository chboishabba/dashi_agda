#!/usr/bin/env python3
"""K04d finite algebra regression: exp(-sum X^k/k) = 1-X modulo X^(N+1).

Exact rational polynomial calculation, no floating point or symbolic-CAS
assumptions. This is NOT a constructive Bishop convergence/series-composition
proof and NOT an Agda kernel receipt. It supplies an independently checkable
finite target for the original native negative-log exponential identity.

Mathematics: Newton formal series; Bishop/Bridges constructive analysis.
"""

import argparse
from fractions import Fraction
from math import factorial


def multiply_truncated(left, right, degree):
    result = [Fraction(0)] * (degree + 1)
    for i, a in enumerate(left):
        if not a or i > degree:
            continue
        for j, b in enumerate(right[: degree + 1 - i]):
            if b:
                result[i + j] += a * b
    return result


def truncated_exponential(zero_constant_poly, degree):
    if zero_constant_poly[0]:
        raise ValueError("The input polynomial must have zero constant term")
    result = [Fraction(0)] * (degree + 1)
    power = [Fraction(0)] * (degree + 1)
    power[0] = Fraction(1)
    for j in range(degree + 1):
        inverse_factorial = Fraction(1, factorial(j))
        for k in range(degree + 1):
            result[k] += inverse_factorial * power[k]
        power = multiply_truncated(power, zero_constant_poly, degree)
    return result


def verify_degree(degree):
    negative_log = [Fraction(0)] + [
        Fraction(-1, k) for k in range(1, degree + 1)
    ]
    actual = truncated_exponential(negative_log, degree)
    expected = [Fraction(1)] + (
        [Fraction(-1)] + [Fraction(0)] * (degree - 1)
        if degree else []
    )
    assert actual == expected, (
        f"K04d formal power-series coefficient failure at N={degree}: "
        f"{[(k, a, b) for k, (a, b) in enumerate(zip(actual, expected)) if a != b]}"
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--through-degree", type=int, default=32)
    args = parser.parse_args()
    if args.through_degree < 0:
        parser.error("--through-degree must be nonnegative")
    for degree in range(args.through_degree + 1):
        verify_degree(degree)
    print(
        f"PASS: {args.through_degree + 1} exact rational truncated-exp/log "
        f"identities (N=0..{args.through_degree})"
    )
    print(
        "Finite Q[X]/(X^(N+1)) regression ONLY; actual Bishop real "
        "series composition, limit transport and Agda acceptance remain OPEN."
    )


if __name__ == "__main__":
    main()
