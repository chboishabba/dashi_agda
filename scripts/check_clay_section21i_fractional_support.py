#!/usr/bin/env python3
"""Finite original-support fractional packing checks; not Lean kernel acceptance."""
from fractions import Fraction
from itertools import combinations, product

checks = 0
for n in range(1, 5):
    universe = range(n)
    supports = [frozenset(c) for k in range(1, n+1)
                for c in combinations(universe, k)]
    families = [supports[i:i+min(4,len(supports)-i)]
                for i in range(len(supports))]
    for fam in families:
        m = len(fam)
        for nums in product(range(4), repeat=m):
            weights = [Fraction(i,4) for i in nums]
            loads = {j: sum((weights[k] for k,s in enumerate(fam) if j in s), Fraction(0))
                     for j in universe}
            if any(x > 1 for x in loads.values()):
                continue
            total = sum(weights, Fraction(0))
            for mask in range(1 << n):
                read = {j for j in universe if mask >> j & 1}
                if any(not(s & read) for s in fam):
                    continue
                assert total <= len(read), (n, fam, weights, read)
                checks += 1
print(f"Fractional original-support checks: {checks}/{checks} PASS")
