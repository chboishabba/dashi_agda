#!/usr/bin/env python3
"""Exact Gaussian-rational finite regression for native Bishop P2 source-scale weld.

This checks the algebra but NOT Agda elaboration, native log/exponential
source scaling, analytic eta continuation, or a Bishop convergence modulus.
"""
from fractions import Fraction as Q
from functools import lru_cache
from random import Random

def add(a, b): return (a[0] + b[0], a[1] + b[1])
def neg(a): return (-a[0], -a[1])
def mul(a, b):
    return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
zero = (Q(0), Q(0))

def test(q, seeds, cutoff):
    @lru_cache(None)
    def term(k):
        if k % 2:
            return mul(q, term((k-1)//2))
        return seeds[k//2]
    eta = even = full = prefix = zero
    for n in range(cutoff):
        a, b = term(2*n), term(2*n+1)
        eta = add(eta, add(a, neg(b)))
        even = add(even, b)
        full = add(full, add(a, b))
        prefix = add(prefix, term(n))
        assert b == mul(q, term(n))
        assert even == mul(q, prefix)
        assert add(eta, add(even, even)) == full
        assert add(eta, add(mul(q, prefix), mul(q, prefix))) == full
    assert even == mul(q, prefix)

def run():
    rng = Random(20261112)
    cases = 0
    for cutoff in range(26):
        for _ in range(36):
            q = (Q(rng.randint(-7,7),rng.randint(1,11)),
                 Q(rng.randint(-7,7),rng.randint(1,11)))
            seeds = [(Q(rng.randint(-9,9),rng.randint(1,13)),
                      Q(rng.randint(-9,9),rng.randint(1,13)))
                     for _ in range(max(1,cutoff))]
            test(q, seeds, cutoff)
            cases += 1
    q = (Q(1,2), Q(1,3))
    a0 = (Q(2), Q(-1))
    correct = mul(q, a0)
    altered = add(correct, (Q(1,7), Q(0)))
    assert altered != correct
    assert add(a0, neg(altered)) != add(a0, neg(correct))
    print(f"PASS: {cases} exact Gaussian-rational finite-prefix cases (cutoffs 0..25)")
    print("PASS: source-scaling negative control")
    print("LIMIT: no native analytic scaling or kernel certification")

if __name__ == "__main__":
    run()
