#!/usr/bin/env python3
"""Euler positive arctangent vs paired Taylor vs original Machin binary split.

Finite exact rational regression, NOT a same-Bishop-real theorem. The Euler
series uses a distinct infinite-series transformation and must not be treated
as an equality of finite Taylor prefixes.
Attribution: Euler's arctangent transformation; Machin (1706);
Bishop/Bridges; Murray/Csimma; existing DASHI Bishop arctangent owners.
"""
from fractions import Fraction
from math import factorial
from statistics import median
from time import perf_counter

from check_bishop_fast_pi_binary_split import (
    MACHIN, atan_split, atan_naive, schedule
)

def generic_split(ratio, a, b):
    if a >= b:
        return (1, 1, 0)
    if b-a == 1:
        p, q = ratio(a)
        return (p, q, p)
    m = (a+b)//2
    p1, q1, t1 = generic_split(ratio, a, m)
    p2, q2, t2 = generic_split(ratio, m, b)
    return (p1*p2, q1*q2, t1*q2+p1*t2)

def euler_sum(q, n):
    """q/(q²+1) Σ 4^k (k!)² / [(2k+1)!(q²+1)^k]."""
    if n == 0:
        return Fraction(0)
    d = q*q+1
    _, den, num = generic_split(
        lambda k: (q, d) if k == 0 else (2*k, (2*k+1)*d),
        0, n
    )
    return Fraction(num, den)

def euler_bounds(q, n):
    """Positive series; tail ≤ next term /(1-1/(q²+1))."""
    d = q*q+1
    lower = euler_sum(q, n)
    next_term = Fraction(q*4**n*factorial(n)**2,
                         d**(n+1)*factorial(2*n+1))
    upper = lower+next_term*Fraction(d, d-1)
    return lower, upper

def euler_schedule(q, coefficient, digits, parts=2):
    """Sufficient bound |c| q/[d^n(d-1)] ≤ 10^-digits / parts."""
    d = q*q+1
    n, power = 0, 1
    while abs(coefficient)*parts*10**digits*q > (d-1)*power:
        n += 1
        power *= d
    return n

def pair_sum(q, count):
    """Pair Taylor indices 2j and 2j+1; exact even-prefix equality."""
    def A(j):
        return (4*j+3)*q*q-(4*j+1)
    def ratio(j):
        if j == 0:
            return (A(0), 3*q**3)
        return (
            A(j)*(4*j-3)*(4*j-1),
            A(j-1)*(4*j+1)*(4*j+3)*q**4
        )
    _, den, num = generic_split(ratio, 0, count)
    return Fraction(num, den)

def test():
    for q in (5, 57, 239, 682):
        for n in range(1, 15):
            assert pair_sum(q, n) == atan_naive(q, 2*n)
            lower, upper = euler_bounds(q, n)
            assert lower < atan_split(q, 40) < upper
    for digits in (20, 100, 1000):
        for coefficient, q in MACHIN:
            n = euler_schedule(q, coefficient, digits)
            lower, upper = euler_bounds(q, n)
            assert abs(coefficient)*(upper-lower) <= Fraction(1, 2*10**digits)
    print("PASS exact paired-prefix equality and Euler positive-tail certificates")

def benchmark():
    test()
    for digits in (100, 1000, 3000, 10000):
        baseline = schedule(MACHIN, digits)
        euler = [euler_schedule(q, c, digits) for c, q in MACHIN]
        output = {}
        methods = (
            ("TaylorBinarySplit", atan_split, baseline),
            ("PairedTaylorBinarySplit",
             lambda q, n: pair_sum(q, (n+1)//2), baseline),
            ("EulerBinarySplit", euler_sum, euler)
        )
        for label, evaluation, counts in methods:
            times = []
            for _ in range(7):
                t0 = perf_counter()
                values = [evaluation(q, n)
                          for (_, q), n in zip(MACHIN, counts)]
                assert len(values) == len(MACHIN)
                times.append(perf_counter()-t0)
            output[label] = {
                "median_ms": round(1000*median(times), 3),
                "terms": sum(counts)
            }
        print(digits, output)

if __name__ == "__main__":
    benchmark()
