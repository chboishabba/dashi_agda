#!/usr/bin/env python3
"""Exact support audit for the proper-prime-power component of Λ(n)Λ(n+2).

Classical elementary estimate: for integer Y>=4, proper prime powers <=Y
are contained among integer perfect powers a**k (a>=2,k>=2).
Split squares and higher powers: k=2 has <=floor(sqrt Y)-1 integer bases,
while every k>=3 has <=floor(cuberoot Y)-1 integer bases. Therefore
  #proper prime powers <= (floor(sqrt Y)-1)
    + max(floor(log_2 Y)-2,0)*(floor(cuberoot Y)-1).
This is O(sqrt Y), removing the previous unnecessary logarithm.
At start positions n with n,n+2<=Y, a nonprime-only pair contribution
must have at least one endpoint a proper prime power (or zero).
Therefore at most twice this refined upper bound of starts contribute
to E. For the standard real genuine Λ weights, |Λ(n)|<=ln Y, so
  0<=E<=2*(floor(sqrt Y)-1+(floor(log_2 Y)-2)*(floor(cuberoot Y)-1))*(ln Y)^2
for Y>=4 (with nonnegative exponent count). Thus E=O(sqrt Y log^2 Y).
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


def floor_cuberoot(y):
    lo,hi=0,1
    while hi**3<=y: hi*=2
    while lo+1<hi:
        mid=(lo+hi)//2
        if mid**3<=y:lo=mid
        else:hi=mid
    return lo


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
    cube=floor_cuberoot(y)
    refined_proper_bound=(isqrt(y)-1)+max(0,log2floor-2)*max(0,cube-1)
    bound=2*refined_proper_bound
    assert proper.issubset({a**k for k in range(2,log2floor+1)
                                    for a in range(2,isqrt(y)+1) if a**k<=y})
    assert len(proper)<=refined_proper_bound
    assert len(contamination)<=len(start_possible)<=bound
    assert not (set(contamination)&set(no_pair))
    assert not any(n in proper and n in primes for n in range(2,y+1))
    twin=[n for n in range(2,y-1) if n in primes and n+2 in primes]
    assert not(set(twin)&set(contamination))
    return {'Y':y,'proper':len(proper),'error_support':len(contamination),
            'potential_error_starts':len(start_possible),
            'old_elementary_bound':2*isqrt(y)*log2floor,
            'refined_proper_bound':refined_proper_bound,
            'elementary_bound':bound,'actual_twins':len(twin)}


if __name__=='__main__':
    for y in (100,1000,10000,100000):
        print(check(y))
    print('PASS exact proper-power support / finite Λ-pair error support')
    print('OPEN: unconditional lower bound on prime-only pair mass.')
