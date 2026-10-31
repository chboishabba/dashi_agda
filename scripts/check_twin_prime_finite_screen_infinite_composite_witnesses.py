#!/usr/bin/env python3
"""Infinite false-positive family for EVERY fixed finite twin-prime sieve.

Given a finite set of screening primes F containing 2 and 3, let
W=prod(F). The class n=-1 mod W survives both local tests
p∤n and p∤n+2 for every p∈F (for p=2, -1 is odd).
Choose two distinct new primes P,Q∉F.
CRT gives a unique n0 mod W*P*Q satisfying
    n=-1 mod W, n=0 mod P, n=-2 mod Q.
For every integer t>=1, n=n0+t*W*P*Q passes the F screen,
while n and n+2 are BOTH composite (proper divisors P,Q).
Thus no fixed finite sieve—including the 15 SSP primes—proves
primality or yields twin-prime infinitude from survivor density alone.

Math: elementary Chinese remainder theorem, original classical source.
Implementation: independent finite witness, not an infinite Agda kernel proof.
"""
from math import prod,isqrt

SSP15=(2,3,5,7,11,13,17,19,23,29,31,41,47,59,71)

def prime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))

def next_prime_after(n):
    p=n+1
    while not prime(p):p+=1
    return p

def merge_crt(a,m,b,n):
    assert m>0 and n>1
    assert all(m%p or n%p for p in range(2,isqrt(min(m,n))+1))
    # The caller supplies pairwise-coprime moduli. pow inverse rejects
    # a non-coprime input instead of silently inventing a CRT section.
    k=((b-a)*pow(m,-1,n))%n
    return (a+m*k)%(m*n),m*n

def false_positive_family(screen,t=1):
    primes=tuple(sorted(set(screen)))
    assert primes and all(prime(p) for p in primes)
    assert 2 in primes and 3 in primes
    W=prod(primes)
    P=next_prime_after(max(primes))
    Q=next_prime_after(P)
    residue,period=merge_crt(W-1,W,0,P)
    residue,period=merge_crt(residue,period,-2,Q)
    n=residue+t*period
    assert t>=1 and n>P and n+2>Q
    assert all(n%p and (n+2)%p for p in primes)
    assert n%P==0 and (n+2)%Q==0
    return {"screen_size":len(primes),"P":P,"Q":Q,
            "period_bits":period.bit_length(),"n_bits":n.bit_length(),
            "n":n}

if __name__=="__main__":
    for screen in ((2,3),(2,3,5,7),SSP15):
        example=false_positive_family(screen)
        print("PASS infinite CRT family witness:",example)
