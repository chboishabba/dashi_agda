#!/usr/bin/env python3
"""P0 exact finite label reference, NOT Agda acceptance.

Original 4D side2 coarse bond order, side4 fine positive bonds,
original two consecutive axial links and unchanged canonical spectators.
Both membership decisions are modeled independently (linear Boolean
scan F19 vs set-based source R445). No imported Gaussian model.
"""
from itertools import product

def bonds(side):
    return [(site, axis) for site in product(range(side), repeat=4)
            for axis in range(4)]

canonical = bonds(4)
coarse = bonds(2)
selected = []
for site, axis in coarse:
    start = tuple(2 * x for x in site)
    next_site = list(start)
    next_site[axis] = (next_site[axis] + 1) % 4
    selected += [(start, axis), (tuple(next_site), axis)]
assert len(coarse) == 64
assert len(selected) == len(set(selected)) == 128

f19_residual = [x for x in canonical if all(x != y for y in selected)]
r445_residual = [x for x in canonical if x not in set(selected)]
assert len(f19_residual) == len(r445_residual) == 896
assert f19_residual == r445_residual
target = selected + f19_residual
assert len(target) == len(set(target)) == len(canonical) == 1024

bond_index = {bond: i for i, bond in enumerate(canonical)}
forward = [bond_index[b] for b in target]
inverse = [None] * 1024
for j, bond in enumerate(target):
    inverse[bond_index[bond]] = forward[j]
assert inverse == list(range(1024))

reverse_pairs = [selected[j + 1] if j % 2 == 0 else selected[j - 1]
                 for j in range(128)] + f19_residual
assert sum(a != b for a, b in zip(target, reverse_pairs)) == 128
print("PASS original F19/R445 P0 128 selected + 896 residual + 1024 inverse")
print("PASS wrong first/second native link orientation: 128 mismatches")
print("NOTE: independent finite Python, not original checked-out Agda kernel")
