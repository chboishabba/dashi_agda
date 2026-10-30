#!/usr/bin/env python3
"""Exact support audit for the proper-prime-power component of Λ(n)Λ(n+2).

Classical elementary estimate: for integer Y>=4, proper prime powers <=Y
are contained among integer perfect powers a**k (a>=2,k>=2).
Each exponent k<=floor(log_2 Y) has at most floor(sqrt(Y)) bases, so
  #proper powers <= floor(sqrt(Y))*floor(log_2 Y).
At start positions n with n,n+2<=Y, a nonprime-only pair contribution
must have at least one endpoint a proper prime power (or zero).
Therefore at most 2*floor(sqrt(Y))*floor(log_2 Y) start positions
contribute to E. For real genuine Λ weights, |Λ(n)|<=ln Y, so
  |E| <= 2*floor(sqrt(Y))*floor(log_2 Y)*(ln Y)^2.
This standard elementary majorant is NOT a twin-prime main-term lower bound
and must not be conflated with a proof of nonzero prime-only correlation.

Exact integer enumeration here tests SUPPORT cardinalities and verifies the
nine exhaustive prime-power pair cases; no floating-point analytic bound
is presented as a machine-checkable theorem.
"""
from math import isqrt


def primes_up_to(n):
    sieve = bytearray(b'\x01')*(n+1)
    sieve[:2]=b'\x00\x00'
    for p in range(2,isqrt(n)+1):
        if sieve[p]:
            sieve[p*p:n+1:p] = b'\x00'*(((n-p*p)//p)+1)
    return {i for i in range(2,n+1) if sieve[i]}


def actual_proper_powers(y):
    ps=primes_up_to(isqrt(y))
    out=set()
    for p in ps:
        x=p*p
        while x<=y:
            out.add(x)
            x*=p
    return out


def check(y):
    assert y>=4
    primes=primes_up_to(y)
    proper=actual_proper_powers(y)
    all_power=primes|proper
    contamination=[n for n in range(2,y-1)
                   if n in all_power and n+2 in all_power and
                   (n in proper or n+2 in proper)]
    start_possible=[n for n in range(2,y-1)
                    if n in proper or n+2 in proper]
    no_pair=[n for n in range(2,y-1)
             if n not in all_power or n+2 not in all_power]
    log2floor=y.bit_length()-1
    bound=2*isqrt(y)*log2floor
    assert proper.issubset({a**k for k in range(2,log2floor+1)
                                    for a in range(2,isqrt(y)+1) if a**k<=y})
    assert len(proper)<=isqrt(y)*log2floor
    assert len(contamination)<=len(start_possible)<=bound
    assert not (set(contamination)&set(no_pair))
    assert not any(n in proper and n in primes for n in range(2,y+1))
    twin=[n for n in range(2,y-1) if n in primes and n+2 in primes]
    assert not(set(twin)&set(contamination))
    return {'Y':y,'proper':len(proper),'error_support':len(contamination),
            'potential_error_starts':len(start_possible),
            'elementary_bound':bound,'actual_twins':len(twin)}


if __name__=='__main__':
    for y in (100,1000,10000,100000):
        print(check(y))
    print('PASS exact proper-power support / finite Λ-pair error support')
    print('OPEN: unconditional lower bound on prime-only pair mass.')
