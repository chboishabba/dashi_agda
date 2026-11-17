#!/usr/bin/env python3
"""CT15a exact symbolic Möbius/divisor expansion of gap-two Lambda.

For each n, Lambda(n) as coefficients of formal log(p) equals
sum_{d|n} mu(d) log(n/d).  Multiply the two independently expanded
factors at shifts n and n+2, keeping ALL positive and negative signed
terms, and require exact formal coefficient equality.

This is an exact finite algebraic identity/diagnostic, NOT a new
positive correlation bound, not a parity barrier bypass, and not
evidence of unconditional twin-prime infinitude.

Mathematical authorship: classical Möbius inversion / von Mangoldt.
Original DASHI prior art: RiemannPrimePowerCounting.MobiusScalarKernel,
PrimeCountingTransforms (parametric analytic bridges), original
RiemannVonMangoldtSpecification; no ESD modifications.
"""
from collections import Counter
from functools import lru_cache
from math import gcd, isqrt

@lru_cache(None)
def factor(n):
    rem, ans = n, {}
    for p in range(2, isqrt(rem) + 1):
        while rem % p == 0:
            ans[p] = ans.get(p, 0) + 1
            rem //= p
    if rem > 1:
        ans[rem] = ans.get(rem, 0) + 1
    return ans

@lru_cache(None)
def mu(n):
    powers = factor(n).values()
    return 0 if any(v > 1 for v in powers) else (-1) ** len(factor(n))

@lru_cache(None)
def divisors(n):
    return tuple(d for d in range(1, n + 1) if n % d == 0)

def direct_lambda_coeff(n):
    fs = factor(n)
    return Counter({next(iter(fs)):1}) if len(fs) == 1 else Counter()

def mobius_lambda_coeff(n):
    coeff = Counter()
    for d in divisors(n):
        sign = mu(d)
        if sign:
            for p, power in factor(n//d).items():
                coeff[p] += sign * power
    return Counter({p:w for p,w in coeff.items() if w})

def shifted_pair_expanded(n):
    coeff = Counter()
    positive = negative = 0
    for d in divisors(n):
        a = mu(d)
        if not a:
            continue
        for e in divisors(n+2):
            b = mu(e)
            if not b:
                continue
            # Necessary CRT condition, not a density theorem:
            assert 2 % gcd(d,e) == 0
            sign = a*b
            for p,u in factor(n//d).items():
                for q,v in factor((n+2)//e).items():
                    coeff[(p,q)] += sign*u*v
                    if sign > 0:
                        positive += u*v
                    else:
                        negative += u*v
    return Counter({w:c for w,c in coeff.items() if c}),positive,negative

def audit():
    receipts = []
    for x in (2,3,5,10,59,100,270,500):
        positive = negative = 0
        for n in range(x,2*x):
            assert mobius_lambda_coeff(n) == direct_lambda_coeff(n)
            expanded,p,m = shifted_pair_expanded(n)
            direct = Counter({(a,b):1
                for a in direct_lambda_coeff(n)
                for b in direct_lambda_coeff(n+2)})
            assert expanded == direct
            positive += p
            negative += m
        receipts.append((x,positive,negative,positive-negative))
    assert receipts[-1] == (500,34943,34930,13)
    print({"status":"PASS","dyadic_windows":8,
           "signed_divisor_expansion_receipts":receipts,
           "analytic_remainder_estimate_proved":False,
           "twin_prime_infinitude_proved":False})

if __name__ == "__main__":
    audit()
