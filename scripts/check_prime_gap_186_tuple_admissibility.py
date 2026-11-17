#!/usr/bin/env python3
"""Independent integer-only admissibility screening for OpenAI's 2026 40-tuple.

Tuple originates from openai/PrimeGaps186 Challenge.lean (Apache 2.0).
Local screening + cardinal argument checks the tuple's admissibility.
It does not verify DHL[40,2], analytic axioms, or infinitely many gaps.
"""
from math import isqrt
H=(0,2,6,12,20,26,30,32,36,42,48,50,56,60,68,72,78,86,90,92,
   98,102,110,116,120,126,132,138,140,146,152,156,158,162,
   168,170,176,180,182,186)

def prime(p):
    return p>=2 and all(p%d for d in range(2,isqrt(p)+1))

def check():
    assert len(H)==len(set(H))==40
    assert tuple(sorted(H))==H
    assert min(H)==0 and max(H)==186
    table={}
    for p in range(2,41):
        if prime(p):
            seen={x%p for x in H}
            missing=[r for r in range(p) if r not in seen]
            assert missing, f'not admissible modulo {p}'
            table[p]=missing[0]
    assert tuple(table)==(2,3,5,7,11,13,17,19,23,29,31,37)
    # For any prime p>40, a 40-element set covers <=40<p residues.
    for p in range(41,257):
        if prime(p):
            assert len({x%p for x in H})<p
    print('OpenAI 186-shift tuple: 40 distinct shifts, diameter 186: PASS')
    print('All primes <=40 checked:', table)
    print('p>40 is admitted by cardinality bound 40<p, not finite sampling alone')
    print('Does not establish DHL[40,2], axiom discharge or twin-prime infinitude')

if __name__=='__main__':check()
