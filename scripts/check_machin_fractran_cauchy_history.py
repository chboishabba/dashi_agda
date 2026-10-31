#!/usr/bin/env python3
"""Exact nonconstant Cauchy sequence of rational Machin-pi approximants.

q_n = 16 Σ_{j<n} (-1)^j/((2j+1)5^(2j+1))
    - 4 Σ_{j<n} (-1)^j/((2j+1)239^(2j+1)).
The alternating remainder guarantees
|q_n-π| <= e_n = 16/((2n+1)5^(2n+1))+4/((2n+1)239^(2n+1))
             <= 4/25^n for n>=1.
Consequently |q_j-q_k| <= 8/25^n whenever j,k>=n.
Each difference q_(n+1)-q_n is nonzero (compare 4*239^(2n+1)
against 5^(2n+1)); every rational stage admits a finite signed
prime-exponent representation, with non-SSP primes in a residual tail.
No claim of an Agda-kernel Bishop-real identification or Pickover sign.
"""
from fractions import Fraction as F

def q(n):
    assert n>=1
    return 16*sum((F((-1)**j,(2*j+1)*5**(2*j+1)) for j in range(n)),F())-4*sum((F((-1)**j,(2*j+1)*239**(2*j+1)) for j in range(n)),F())

def error(n):
    assert n>=1
    return F(16,(2*n+1)*5**(2*n+1))+F(4,(2*n+1)*239**(2*n+1))

def step(n):
    assert n>=1
    return F((-1)**n,2*n+1)*(F(16,5**(2*n+1))-F(4,239**(2*n+1)))

def check():
    for n in range(1,25):
        assert q(n+1)-q(n)==step(n)
        assert step(n)!=0
        assert error(n)<=F(4,25**n)
        assert error(n+1)<error(n)
    print("PASS exact rational history, nonconstant steps, geometric error envelope")
if __name__=="__main__":
    check()
