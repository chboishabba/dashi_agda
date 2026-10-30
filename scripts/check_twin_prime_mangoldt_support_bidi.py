#!/usr/bin/env python3
"""Local executable oracle for M14 actual Lambda support / residual BIDI.
Formal monomials (p,q) stand for log(p)log(q); no floating assumptions.
This is NOT an Agda kernel receipt, nor an analytic lower-bound proof.
Attribution: original von Mangoldt and prime-power arithmetic;
DASHI RiemannVonMangoldtSpecification and RiemannPrimePowerCounting.
"""
from math import isqrt

def power_base(n):
    if n < 2: return None
    for p in range(2, isqrt(n)+1):
        if n % p: continue
        t = n
        while t % p == 0: t //= p
        return p if t == 1 else None
    return n

def independent_base(n):
    if n < 2: return None
    facts = []
    x = n
    for p in range(2, isqrt(n)+1):
        if x%p == 0:
            exponent = 0
            while x%p == 0:
                x //= p
                exponent += 1
            facts.append((p, exponent))
    if x > 1: facts.append((x,1))
    return facts[0][0] if len(facts) == 1 else None

def pair(n):
    a, b = power_base(n), power_base(n+2)
    return (a,b) if a is not None and b is not None else None

def main():
    counts = {"outside":0,"left":0,"right":0,"both":0}
    for n in range(25000):
        a, b = power_base(n), power_base(n+2)
        assert a == independent_base(n)
        assert b == independent_base(n+2)
        assert pair(n) == pair(270 * (n//270) + n%270)
        if a is not None: counts["left"] += 1
        if b is not None: counts["right"] += 1
        if a is not None and b is not None: counts["both"] += 1
        if a is None or b is None: counts["outside"] += 1
    tests = 0
    for p in (2,3,5,7,11,13,17,19,23,29,31):
        for e in range(2,8):
            assert power_base(p**e) == p
            tests += 1
    assert pair(59) == (59,61)
    assert pair(209) is None and pair(329) is None
    print({"status":"PASS","nat_pairs":25000,"proper_powers":tests,
           "counts":counts,"kernel_checked":False,"positive_lower_bound":False})
if __name__ == "__main__":
    main()
