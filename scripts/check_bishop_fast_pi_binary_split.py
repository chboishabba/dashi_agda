#!/usr/bin/env python3
"""Exact rational Machin finite sums by integer binary splitting.

Reference computation only; the Agda proof of equivalence to
BishopMachinArctanConstructionExact remains an explicit obligation.
Attribution: Machin (1706); Bishop/Bridges; Murray/Csimma;
DASHI's existing Bishop arctangent construction.
"""
from fractions import Fraction
from time import perf_counter
import argparse
import json
import sys

sys.set_int_max_str_digits(0)

MACHIN = ((16, 5), (-4, 239))
FOUR_TERM = ((176, 57), (28, 239), (-48, 682), (96, 12943))

def term_ratio(k, q):
    if k == 0:
        return 1, q
    return -(2*k-1), (2*k+1)*q*q

def split(q, a, b):
    """(P,Q,T): P/Q product of term ratios, T/Q relative prefix sum."""
    if a >= b:
        return 1, 1, 0
    if b-a == 1:
        p, d = term_ratio(a, q)
        return p, d, p
    m = (a+b)//2
    p1, q1, t1 = split(q, a, m)
    p2, q2, t2 = split(q, m, b)
    return p1*p2, q1*q2, t1*q2+p1*t2

def atan_split(q, n):
    _, d, t = split(q, 0, n)
    return Fraction(t, d)

def atan_naive(q, n):
    return sum((Fraction((-1)**k, (2*k+1)*q**(2*k+1))
                for k in range(n)), Fraction(0))

def atan_bounds(q, n):
    s = atan_split(q, n)
    next_term = Fraction((-1)**n, (2*n+1)*q**(2*n+1))
    return min(s, s+next_term), max(s, s+next_term)

def schedule(formula, digits):
    target = 10**digits
    count = len(formula)
    ns = []
    for c, q in formula:
        n, power = 0, q
        while abs(c)*count*target > (2*n+1)*power:
            n += 1
            power *= q*q
        ns.append(n)
    return ns

def enclosure(formula, ns):
    lower = upper = Fraction(0)
    for (c, q), n in zip(formula, ns):
        lo, hi = atan_bounds(q, n)
        if c >= 0:
            lower += c*lo
            upper += c*hi
        else:
            lower += c*hi
            upper += c*lo
    return lower, upper

def verify():
    for q in (3, 5, 57, 239, 682, 12943):
        for n in range(19):
            assert atan_split(q, n) == atan_naive(q, n)
            for a in range(n+1):
                p, d, t = split(q, a, n)
                product, total = Fraction(1), Fraction(0)
                for k in range(a, n):
                    num, den = term_ratio(k, q)
                    product *= Fraction(num, den)
                    total += product
                assert Fraction(p, d) == product
                assert Fraction(t, d) == total
    for d in (20, 100, 1000):
        la, ua = enclosure(MACHIN, schedule(MACHIN, d))
        lb, ub = enclosure(FOUR_TERM, schedule(FOUR_TERM, d))
        assert la <= ub and lb <= ua
        assert ua-la <= Fraction(1, 10**d)
        assert ub-lb <= Fraction(1, 10**d)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--digits", type=int, nargs="*", default=[100, 1000, 10000])
    args = parser.parse_args()
    verify()
    results = []
    for digits in args.digits:
        for label, formula in (("Machin2", MACHIN), ("FourTerm", FOUR_TERM)):
            start = perf_counter()
            ns = schedule(formula, digits)
            t1 = perf_counter()
            lo, hi = enclosure(formula, ns)
            t2 = perf_counter()
            assert lo <= hi and hi-lo <= Fraction(1, 10**digits)
            results.append(dict(method=label, digits=digits, terms=sum(ns),
                                terms_by_argument=ns,
                                scheduling_seconds=t1-start,
                                exact_enclosure_seconds=t2-t1,
                                total_seconds=t2-start,
                                interval_width_bound=f"10^-{digits}"))
    print(json.dumps(results, indent=2))

if __name__ == "__main__":
    main()
