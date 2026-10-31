#!/usr/bin/env python3
"""Prime-power contamination: explicit unconditional shifted-Mangoldt bound.

For integer X>=4 let T(X)=sum_{2<=n<=X-2} Lambda(n)Lambda(n+2),
P(X)=sum_{n,n+2 primes <=X} log(n)log(n+2), E=T-P.

Define Q(X)=the count of distinct proper prime powers p^k<=X, k>=2.
Every non-prime-only nonzero summand has at least one endpoint in Q(X).
Each proper power can occur as n or n+2 at most once per endpoint.
Hence 0<=E<=2 Q(X)(log X)^2.
Every proper prime power is a^k for k>=2, a>=2; k<=floor(log2 X).
Counting all integer bases (overcounting composites) gives
Q(X)<=sum_{k=2}^{floor(log2 X)} floor(X^(1/k))
    <= floor(sqrt(X)) * floor(log2 X).
Thus E<=2 floor(sqrt(X)) floor(log2 X) (log X)^2=o(X).
This is an actual analytic reduction, NOT unbounded twin-prime correlation.

A finite integer combinatorial certificate avoids floating log calculations:
sum of indicator contamination <=2Q; the real log bound then follows.
"""
from math import isqrt

def proper_prime_powers(X):
    # Naive deterministic primality for finite cross-check, not proof oracle.
    def prime(p):
        return p>=2 and all(p%d for d in range(2,isqrt(p)+1))
    out=set()
    for p in range(2,isqrt(X)+1):
        if prime(p):
            n=p*p
            while n<=X:
                out.add(n)
                n*=p
    return out

def verify(X):
    assert X>=4
    pp=proper_prime_powers(X)
    log2_floor=X.bit_length()-1
    assert len(pp)<=isqrt(X)*log2_floor
    # Every contaminating nonzero Lambda pair has a proper power endpoint.
    # Check the sharper combinatorial incidence bound (nonzero
    # prime-power pair summands counted at most twice).
    def primepower(n):
        if n<2:return False
        for p in range(2,n+1):
            if n%p==0 and all(p%d for d in range(2,isqrt(p)+1)):
                while n%p==0:n//=p
                return n==1
        return False
    affected=sum(1 for n in range(2,X-1)
                 if primepower(n) and primepower(n+2)
                 and (n in pp or n+2 in pp))
    assert affected<=2*len(pp)
    return (X,len(pp),affected,2*isqrt(X)*log2_floor)

if __name__=="__main__":
    for X in (4,10,100,1000):
        print("PASS X, proper powers, contaminated pairs, bound:",verify(X))
