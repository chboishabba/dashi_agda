#!/usr/bin/env python3
"""Exact count-class Bayes risk for the source-owned NV binary photon model.

A conditional-iid mathematical model, not a calibrated NV experiment.
Original NV likelihood owner: diamond MCG #1238. Consumer: #1269.
"""
from fractions import Fraction
from itertools import product
from math import comb

def bayes_error(p, q, n):
    """Equal-prior optimal error; binomial sufficient statistic; O(n)."""
    assert 0 <= p <= 1 and 0 <= q <= 1 and n >= 0
    return sum((comb(n,k)*min(p**k*(1-p)**(n-k),
                             q**k*(1-q)**(n-k))
                for k in range(n+1)), Fraction(0))/2

def chebyshev_bound(p, q, n):
    """Valid two-sided midpoint-threshold upper bound, iid only."""
    if n == 0 or p == q:
        return Fraction(1,2)
    return min(Fraction(1,2),
               2*(p*(1-p)+q*(1-q))/(n*(p-q)**2))

def paired_hellinger_bound(p, q, n):
    """Rational upper bound via Hellinger + Cauchy-Schwarz + pair grouping.

    Pe*(n) <= 1/2 (1-(p-q)^2)^(floor(n/2)).
    This is valid but not necessarily sharp; n=1 bound is trivial.
    """
    return Fraction(1,2)*(1-(p-q)**2)**(n//2)

def exhaustive_error(p,q,n):
    return sum((min(p**sum(h)*(1-p)**(n-sum(h)),
                    q**sum(h)*(1-q)**(n-sum(h)))
                for h in product((0,1),repeat=n)),Fraction(0))/2

def check():
    grid = [Fraction(i,10) for i in range(11)]
    cases = 0
    for n in range(13):
        for p in grid:
            for q in grid:
                e = bayes_error(p,q,n)
                assert e <= chebyshev_bound(p,q,n)
                assert e <= paired_hellinger_bound(p,q,n)
                assert e == bayes_error(q,p,n)
                if p == q: assert e == Fraction(1,2)
                if n <= 6: assert e == exhaustive_error(p,q,n)
                if n > 0: assert e <= bayes_error(p,q,n-1)
                cases += 1
    print("PASS:",cases,"exact rational parameter/depth cases")

if __name__ == "__main__":
    check()
