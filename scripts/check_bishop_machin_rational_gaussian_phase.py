#!/usr/bin/env python3
"""Finite exact Q[i] verification of the K05 Machin Cayley phase.

This independently checks the numeric Gaussian identities used by
BishopMachinRationalGaussianPhaseExact.agda.  It does NOT establish
the actual arctangent/exponential semantic weld or Agda acceptance.
"""
from fractions import Fraction as Q


def mul(z, w):
    return (z[0] * w[0] - z[1] * w[1],
            z[0] * w[1] + z[1] * w[0])


def power(z, n):
    result = (Q(1), Q(0))
    for _ in range(n):
        result = mul(result, z)
    return result


def cayley(t):
    denominator = 1 + t * t
    return ((1 - t * t) / denominator, 2 * t / denominator)


def main():
    a = cayley(Q(1, 5))
    b = cayley(Q(1, 239))
    assert a == (Q(12, 13), Q(5, 13))
    assert b == (Q(28560, 28561), Q(239, 28561))
    a4 = power(a, 4)
    assert a4 == (Q(-239, 28561), Q(28560, 28561))
    assert a[0] * a[0] + a[1] * a[1] == 1
    assert b[0] * b[0] + b[1] * b[1] == 1
    quarter = mul(a4, (b[0], -b[1]))
    assert quarter == (Q(0), Q(1)), quarter
    print("PASS: Machin Gaussian rational Cayley phase")
    print("q5 = 12/13 + 5i/13")
    print("q239 = 28560/28561 + 239i/28561")
    print("q5^4 * conjugate(q239) = i exactly")
    print("FINITE Q[i] IDENTITY ONLY: original Bishop atan/exp weld OPEN")


if __name__ == "__main__":
    main()
