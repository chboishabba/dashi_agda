#!/usr/bin/env python3
"""Exact nonconstant Cauchy sequence of rational Machin-pi approximants.

q_n = 16 Σ_{j<n} (-1)^j/((2j+1)5^(2j+1))
    - 4 Σ_{j<n} (-1)^j/((2j+1)239^(2j+1)).
The alternating remainder guarantees
|q_n-π| <= e_n = 16/((2n+1)5^(2n+1))+4/((2n+1)239^(2n+1))
             <= 4/25^n for n>=0.
Consequently |q_j-q_k| <= 8/25^n whenever j,k>=n.
Each difference q_(n+1)-q_n is nonzero (compare 4*239^(2n+1)
against 5^(2n+1)); every rational stage admits a finite signed
prime-exponent representation, with non-SSP primes in a residual tail.
No claim of an Agda-kernel Bishop-real identification or Pickover sign.
"""
from fractions import Fraction as F

def q(n):
    assert n>=0
    return 16*sum((F((-1)**j,(2*j+1)*5**(2*j+1)) for j in range(n)),F())-4*sum((F((-1)**j,(2*j+1)*239**(2*j+1)) for j in range(n)),F())

def error(n):
    assert n>=0
    return F(16,(2*n+1)*5**(2*n+1))+F(4,(2*n+1)*239**(2*n+1))

def step(n):
    assert n>=0
    return F((-1)**n,2*n+1)*(F(16,5**(2*n+1))-F(4,239**(2*n+1)))

SSP15 = frozenset((2,3,5,7,11,13,17,19,23,29,31,41,47,59,71))

def prime_factors(n):
    assert n > 0
    factors = []
    p = 2
    while p*p <= n:
        while n % p == 0:
            factors.append(p)
            n //= p
        p += 1
    if n > 1:
        factors.append(n)
    assert all(p == 2 or all(p % d for d in range(2, int(p**0.5)+1)) for p in factors)
    return factors

def check():
    # Universal elementary bound (valid for n >= 0):
    # 239^(2n+1) >= 239*25^n, and 2n+1 >= 1.
    # Therefore e_n <= (16/5+4/239)/25^n <= 4/25^n.
    coefficient = F(16,5) + F(4,239)
    assert coefficient == F(3844,1195) and coefficient < 4
    assert q(0) == 0
    for n in range(0,25):
        assert error(n) <= coefficient/F(25**n)
        assert error(n) <= F(4,25**n)
        assert error(n+1) < error(n)
        assert q(n+1)-q(n)==step(n)
        assert step(n)!=0
    for cutoff in range(1,10):
        for j in range(cutoff,cutoff+4):
            for k in range(cutoff,cutoff+4):
                assert abs(q(j)-q(k)) <= error(j)+error(k)
                assert abs(q(j)-q(k)) <= F(8,25**cutoff)
    # Genuine non-SSP primes already occur at q_1. Zero is separately
    # encoded, rather than represented by the empty factor product (=1).
    assert q(1) == F(3804,1195)
    numerator = prime_factors(abs(q(1).numerator))
    denominator = prime_factors(q(1).denominator)
    assert numerator == [2,2,3,317]
    assert denominator == [5,239]
    for factors, value in ((numerator, 3804),(denominator, 1195)):
        product = 1
        for factor in factors:
            product *= factor
        assert product == value
    assert 317 not in SSP15 and 239 not in SSP15
    print("PASS exact Machin q_n, universal geometric-envelope algebra, finite Cauchy pairs, genuine q1 non-SSP residual")

if __name__=="__main__":
    check()
