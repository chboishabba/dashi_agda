#!/usr/bin/env python3
"""Exact unconditional TWO-POINT twin-prime sieve correlation bound.

Arithmetic owner: DASHI/Arithmetic/SixWheelCRTExact.agda,
FinitePrimeProductSieveExact.agda, TwinPrimeSixWheelExact.agda.
Original mathematics: Eratosthenes/Brun/CRT; do NOT credit this
elementary finite sieve as a twin-prime infinitude theorem.

For prime cutoff z>=2, let P_z be primes <=z, k=#P_z,
D_z=(1/2)*prod_{3<=p<=z}(1-2/p).
For X>=z+2 define pi_2(X)=#{n:2<=n,n+2<=X, both primes}.
A prime pair n>z avoids residue classes 0,-2 mod each p<=z.
p=2 has one forbidden residue, all odd p have two.
By CRT and inclusion-exclusion the exact finite survivor count
S(X,z)=#{1<=n<=X : gcd(n(n+2),prod p)=1} obeys

  |S(X,z)-X*D_z| <= 2 * 3**(k-1),

because inclusion-exclusion has 2*3**(k-1) terms and every
single CRT-congruence count differs from its X/modulus expectation
by <1. Thus for every X>=z+2,

  0 <= pi_2(X) <= z + X*D_z + 2*3**(k-1).

This is an unconditional pair-correlation UPPER bound; a LOWER
bound forcing infinitely many twin primes is NOT established.
"""
from fractions import Fraction as F
from math import gcd,isqrt,prod
from itertools import product as cartesian

def prime(n):
    return n>=2 and all(n%d!=0 for d in range(2,isqrt(n)+1))

def primes_le(z):
    return [p for p in range(2,z+1) if prime(p)]

def wheel_density(z):
    ps=primes_le(z)
    assert ps and ps[0]==2
    result=F(1,2)
    for p in ps[1:]:result*=F(p-2,p)
    return result

def finite_pair_survivor(n,ps):
    return all(n%p!=0 and (n+2)%p!=0 for p in ps)

def survivor_count(X,z):
    ps=primes_le(z)
    return sum(finite_pair_survivor(n,ps) for n in range(1,X+1))

def twin_count(X):
    return sum(prime(n) and prime(n+2) for n in range(2,X-1))

def inclusion_exclusion_density(z):
    # Exhaustively recompute the CRT expectation from the actual
    # ternary local selection at each odd prime.
    ps=primes_le(z)
    options=[[None,0]]+[[None,0,-2] for p in ps[1:]]
    total=F()
    terms=0
    for choice in cartesian(*options):
        m=1
        sign=1
        for p,r in zip(ps,choice):
            if r is not None:
                m*=p
                sign=-sign
        total+=F(sign,m)
        terms+=1
    assert terms==2*3**(len(ps)-1)
    return total,terms

def verify(X,z):
    ps=primes_le(z)
    assert X>=z+2 and len(ps)>=1
    density,terms=inclusion_exclusion_density(z)
    assert density==wheel_density(z)
    S=survivor_count(X,z)
    t=twin_count(X)
    assert abs(F(S)-X*density)<=terms
    bound=F(z)+X*density+terms
    assert t<=bound
    return z,X,t,S,str(density),terms,str(bound)

if __name__=="__main__":
    for z,X in ((3,100),(5,1000),(7,10000),(11,10000),(13,100000)):
        print("PASS z,X,twins,survivors,density,terms,bound:",verify(X,z))
