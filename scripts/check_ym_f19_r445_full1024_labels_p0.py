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
# Real inverse of target->canonical permutation, not tautologically
# assigning the canonical index to itself.
inverse = [None] * 1024
for j, canonical_position in enumerate(forward):
    assert inverse[canonical_position] is None
    inverse[canonical_position] = j
assert sorted(inverse) == list(range(1024))
assert all(inverse[forward[j]] == j for j in range(1024))
assert all(forward[inverse[i]] == i for i in range(1024))

reverse_pairs = [selected[j + 1] if j % 2 == 0 else selected[j - 1]
                 for j in range(128)] + f19_residual
assert sum(a != b for a, b in zip(target, reverse_pairs)) == 128
# Independent arbitrary link VALUE evaluation in a non-Abelian
# subgroup Q8 of SU(2). This confirms F19 and R445 preserve the
# complete original field, not merely the selected labels.
MUL={(1,2):(1,3),(2,3):(1,1),(3,1):(1,2),
     (2,1):(-1,3),(3,2):(-1,1),(1,3):(-1,2)}
def qm(left,right):
    sa,ba=left
    sb,bb=right
    if ba==0: return (sa*sb,bb)
    if bb==0: return (sa*sb,ba)
    if ba==bb: return (-sa*sb,0)
    sign,basis=MUL[(ba,bb)]
    return (sa*sb*sign,basis)
reverse_products_differ=0
for config in range(5):
    values=[]
    for i,(site,axis) in enumerate(canonical):
        z=(i*13+sum((5,11,17,23)[p]*v for p,v in enumerate(site))
           +axis*29+config*41)%8
        values.append((1 if z<4 else -1,(z+2*axis+config)%4))
    f19_values=[values[bond_index[b]] for b in selected+f19_residual]
    r445_values=[values[bond_index[b]] for b in selected+r445_residual]
    assert f19_values==r445_values
    reconstructed=[r445_values[inverse[i]] for i in range(1024)]
    assert reconstructed==values
    for j in range(0,128,2):
        forward_product=qm(r445_values[j],r445_values[j+1])
        assert forward_product==qm(f19_values[j],f19_values[j+1])
        reverse_products_differ+=(
            forward_product!=qm(r445_values[j+1],r445_values[j]))
    changed=list(r445_values)
    changed[128+config]=(1,0) if changed[128+config]!=(1,0) else (-1,0)
    assert sum(a!=b for a,b in zip(
        values,[changed[inverse[i]] for i in range(1024)]))==1
assert reverse_products_differ>0
print("PASS original F19/R445 actual arbitrary Q8 link values: 5 x 1024")
print("PASS original noncommutative Q8 blocked products: 320/320")
print("NEGATIVE reversed Q8 pair order:",reverse_products_differ,"different")
print("NEGATIVE altered interacting spectator: 5/5 original fields changed")

print("PASS original F19/R445 P0 128 selected + 896 residual + 1024 inverse")
print("PASS wrong first/second native link orientation: 128 mismatches")
print("NOTE: independent finite Python, not original checked-out Agda kernel")
