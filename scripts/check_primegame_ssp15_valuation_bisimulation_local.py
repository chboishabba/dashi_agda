#!/usr/bin/env python3
"""Local PRIMEGAME integer <-> valuation-vector finite-step regression.

Conway 1987 owns the original prime-generating machine; Guy 1983
owns the tested 14-rule 15/14,15/2 variant. Original DASHI
SignedSSPFRACTRANWeaveExact owns the 15 typed carrier values.
Only TEN of those carriers occur in the 14 historical fractions.
Tests 20000 integer steps and valuation guards/updates against the
existing program fixture. No Agda kernel or signed-VM compiler claim.
"""
from math import prod
from check_fracdash_conway_primegame_offsets import CONWAY_GUY_FOURTEEN

CARRIERS = (2,3,5,7,11,13,17,19,23,29)

def valuation(n):
    v = []
    for p in CARRIERS:
        e = 0
        while n > 1 and n % p == 0:
            n //= p
            e += 1
        v.append(e)
    assert n == 1, ('prime factor outside canonical SSP15 support', n)
    return tuple(v)

def numeric(v):
    assert all(e >= 0 for e in v)
    return prod(p**e for p,e in zip(CARRIERS,v))

def main():
    fractions = CONWAY_GUY_FOURTEEN
    assert len(fractions) == 14 and len(CARRIERS) == 10
    factors = [(valuation(a),valuation(b)) for a,b in fractions]
    n = 2
    vector = valuation(n)
    emitted = []
    visited = set()
    for tick in range(20001):
        assert numeric(vector) == n
        if tick and n > 2 and n & (n-1) == 0:
            emitted.append((tick,n.bit_length()-1))
        if tick == 20000:
            break
        numeric_enabled = [j for j,(a,b) in enumerate(fractions)
                           if n % b == 0]
        vector_enabled = [j for j,(av,bv) in enumerate(factors)
                          if all(x >= y for x,y in zip(vector,bv))]
        assert numeric_enabled == vector_enabled and numeric_enabled
        j=numeric_enabled[0]
        visited.add(j)
        a,b=fractions[j]
        av,bv=factors[j]
        vector=tuple(x+y-z for x,y,z in zip(vector,av,bv))
        n=n//b*a
        assert numeric(vector) == n
    assert emitted == [(19,2),(69,3),(280,5),(707,7),
                       (2363,11),(3876,13),(8068,17),
                       (11319,19),(19201,23)]
    assert len(visited) == len(fractions)
    print('PASS: 14 rules, 10 carriers, 20,000 numeric/valuation step agreements')
    print('PASS: 20,001 state reconstructs, 9 historical prime emissions')
    print('NO: unbounded prime completeness, signed SSP runtime, Agda kernel')

if __name__ == '__main__':
    main()
