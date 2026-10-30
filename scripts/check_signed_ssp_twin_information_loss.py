#!/usr/bin/env python3
"""Finite independent check of DASHI signed orientation / twin predicates.

Pure Python exact arithmetic, NOT an Agda kernel proof. Reuses the mathematical
interpretations of existing SignedSSPFRACTRANWeaveExact and PrimeCountingFunction.
"""
from math import isqrt


def primes_up_to(limit):
    a = bytearray(b'\x01')*(limit+1)
    a[0:2]=b'\x00\x00'
    for p in range(2,isqrt(limit)+1):
        if a[p]:
            a[p*p:limit+1:p]=b'\x00'*((limit-p*p)//p+1)
    return a


def main():
    limit=100000
    isprime=primes_up_to(limit+2)
    twin=lambda n: bool(isprime[n] and isprime[n+2])
    assert twin(3) and twin(5) and not twin(7)
    assert bool(isprime[2]) and not twin(2)
    orientation=lambda n: 'forward' if n>0 else 'mediated'
    assert orientation(5)==orientation(7)=='forward'
    assert twin(5)!=twin(7)
    starts=[n for n in range(2,limit+1) if twin(n)]
    direct=[p for p in range(2,limit+1) if isprime[p] and isprime[p+2]]
    assert starts==direct
    assert len(starts)==1224, len(starts)
    for p in [2,3,5,7,11,13,17,19,37,43,53,71,101,103]:
        assert isprime[p]
        survivors=[r for r in range(p) if r%p and (r+2)%p]
        assert len(survivors)==(1 if p==2 else p-2)
    # 4B-related tag strings are distinct from arithmetic Nat primes.
    # There is no map from a Monster class label to twin primality here.
    print('Twin starts <=100000:',len(starts),'; first 10:',starts[:10])
    print('5 -> positive orientation -> twin: true')
    print('7 -> positive orientation -> twin: false')
    print('p=2 exceptional one-residue survivor; odd p-2 count: PASS')
    print('Exact finite regression: PASS; Agda kernel and infinitude NOT claimed')


if __name__=='__main__':
    main()
