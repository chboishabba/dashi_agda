#!/usr/bin/env python3
"""Type and action audit for canonical DASHI 3x3x3 balanced-ternary cube.

DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact
is the REAL 27 geometric object. Compared here with:
  (a) cyclic Z/27 encoded using signed ternary digits;
  (b) the 3-adic modular B3 matrix on an arbitrarily chosen xy sheet;
  (c) exponent labels of a separate Monster order-27 element.

Cardinality/chart equality does NOT imply graph isometry, group
structure, modular-torus state, or a physical Monster/KK duality.
"""
from itertools import product
from collections import Counter

TRITS=(-1,0,1)
CUBE=set(product(TRITS,repeat=3))
assert len(CUBE)==27

def grid_edge(p,q):
    return sum(p[i]!=q[i] for i in range(3))==1 and sum(abs(p[i]-q[i]) for i in range(3))==1

edges={tuple(sorted((p,q))) for p in CUBE for q in CUBE if grid_edge(p,q)}
assert len(edges)==54
degree=Counter(p for e in edges for p in e)
assert Counter(degree.values())==Counter({3:8,4:12,5:6,6:1})
assert sum(p[2]==0 for p in CUBE)==9
assert len({p for p in CUBE if max(abs(x) for x in p)==1})==26

# Chart bijection by digits, NOT an equivarariance theorem for
# cube graph, and definitely NOT an identification with Monster g.
def encode(p):
    return sum(p[i]*3**i for i in range(3))%27

def decode(n):
    a=n%27
    if a>13:a-=27
    digits=[]
    for _ in range(3):
        r=((a+1)%3)-1
        digits.append(r)
        a=(a-r)//3
    assert a==0
    return tuple(digits)

assert {encode(p) for p in CUBE}==set(range(27))
assert all(decode(encode(p))==p for p in CUBE)
assert all(encode(decode(n))==n for n in range(27))
assert encode((1,1,1))==13 and decode((13+1)%27)==(-1,-1,-1)
assert not grid_edge((1,1,1),(-1,-1,-1))

res=lambda x: ((x+1)%3)-1
def modular_slice(p):
    x,y,z=p
    return (res(x+y),res(x-y),z)

assert {modular_slice(p) for p in CUBE}==CUBE
assert all(modular_slice(modular_slice(p))==(-p[0],-p[1],p[2]) for p in CUBE)
assert all(modular_slice(modular_slice(modular_slice(modular_slice(p))))==p for p in CUBE)
assert grid_edge((0,0,0),(1,0,0))
assert not grid_edge(modular_slice((0,0,0)),modular_slice((1,0,0)))

cycles=[];remaining=set(CUBE)
while remaining:
    start=min(remaining); cur=start; cycle=[]
    while cur not in cycle:
        cycle.append(cur);remaining.remove(cur);cur=modular_slice(cur)
    assert cur==start
    cycles.append(cycle)
assert Counter(map(len,cycles))==Counter({1:3,4:6})
assert {p for p in CUBE if modular_slice(p)==p}=={(0,0,z) for z in TRITS}

# Contrast: addition mod27 is a SINGLE cycle, acting by carry
# which does not preserve nearest-neighbour geometric cube edges.
carry=lambda p:decode((encode(p)+1)%27)
seen=set();x=(0,0,0)
for _ in range(27):
    assert x not in seen
    seen.add(x);x=carry(x)
assert seen==CUBE and x==(0,0,0)

# Order-27 Monster charge data are another TYPED group carrier;
# modular exponents (r,s) live on 27x27=729 labels, not Cube27.
assert 27*27==729

print('PASS Cube27=3x3x3, faces 6, sheets 3x9, edges 54')
print('PASS degree distribution corners=8, edge sites=12, face centres=6, centre=1')
print('PASS cube↔Z/27 digit bijection; carry wraps opposite corners, not graph edge')
print('PASS M on cube xy slices: three fixed z-axis points, six 4-cycles')
print('PASS M action fails geometric edge-preservation')
print('PASS Monster order-27 sector pair has 729 labels; not the cube')

# Stronger, CHART-INDEPENDENT no-go: the 3x3x3 grid graph is bipartite.
# Every one-step edge flips parity of the number of nonzero coordinates.
# An equivariant identification of the 27-cycle of residue +1 with an
# adjacency-preserving motion would require a closed 27-edge walk in
# the cube graph, impossible by parity (all odd cycles are forbidden).
parity=lambda p:sum(abs(t) for t in p)%2
assert all(parity(p)!=parity(q) for p,q in edges)
assert Counter(parity(p) for p in CUBE)==Counter({0:13,1:14})
print('PASS intrinsic no-go: bipartite cube graph has no 27-edge closed cycle')
print('NO chart makes +1 generator on Z/27 an adjacency-preserving 27-cycle on Cube27')

# Graph-aut group computation: every signed coordinate permutation is an
# exact adjacency-preserving bijection; there are precisely 3!*2^3=48.
# To see there are no others: the origin is the unique degree-6 vertex,
# its six degree-5 neighbours are grouped into three opposite pairs.
# Opposite axis neighbours have just one shared neighbour (the origin),
# whereas transverse pairs have two. Every automorphism must permute
# the three pairs and choose an orientation in each -> at most 3!*2^3.
# Since explicit signed permutations attain 48, this is the full group.
from itertools import permutations
def neighbours(p):
    return {q for q in CUBE if grid_edge(p,q)}
origin=(0,0,0)
assert {p for p in CUBE if degree[p]==6}=={origin}
axial=neighbours(origin)
assert len(axial)==6 and all(degree[p]==5 for p in axial)
opposite_pairs={frozenset((p,q)) for p in axial for q in axial
                if p!=q and len(neighbours(p)&neighbours(q))==1}
assert len(opposite_pairs)==3
assert set().union(*opposite_pairs)==axial
actual_automorphisms=set()
for perm in permutations(range(3)):
    for signs in product((-1,1),repeat=3):
        f=lambda p:tuple(signs[i]*p[perm[i]] for i in range(3))
        assert {tuple(sorted((f(p),f(q)))) for p,q in edges}==edges
        actual_automorphisms.add(tuple(f(p) for p in sorted(CUBE)))
assert len(actual_automorphisms)==48
assert 48%27!=0
print('PASS Aut(3x3x3 grid)=signed-axis permutation group, order 48')
print('NO faithful C27 graph-isometry action on the native Cube27')

# The six centre-adjacent axial points distinguish EVERY cube vertex
# by its graph-distance signature. Thus an automorphism is uniquely
# determined by its action on those six points, closing the upper bound.
distance_signature=lambda p:tuple(sum(abs(p[i]-a[i]) for i in range(3))
                                for a in sorted(axial))
assert len({distance_signature(p) for p in CUBE})==27
print('PASS six axial-neighbour distance signatures distinguish all 27 vertices')
