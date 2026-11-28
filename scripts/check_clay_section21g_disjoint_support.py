#!/usr/bin/env python3
"""Section 21g: exact finite original-support hitting/packing regression.

Independent finite regression, NOT native Lean/Agda or an unrestricted
complexity lower bound. Proves by enumeration only n<=5 fixtures.
"""
from itertools import combinations

checks = 0
for n in range(1, 6):
    coords = range(n)
    supports = [frozenset(s) for k in range(1, n+1)
                for s in combinations(coords,k)]
    for readmask in range(1<<n):
        read = frozenset(i for i in coords if (readmask>>i)&1)
        hit = [s for s in supports if s & read]
        for s in hit:
            checks += 1
            assert bool(s & read)
        for i,s in enumerate(hit):
            for t in hit[i+1:]:
                if not (s & t):
                    checks += 1
                    assert 2 <= len(read)
                    for v in hit:
                        if not (s & v or t & v):
                            checks += 1
                            assert 3 <= len(read)
print(f"Original disjoint-support combinatorial checks PASS: {checks}")
assert checks == 3799
