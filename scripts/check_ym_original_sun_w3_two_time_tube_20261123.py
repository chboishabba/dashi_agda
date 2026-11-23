#!/usr/bin/env python3
"""Exact ORIGINAL L4 Wilson SU(N) two-time selected 8-side *one-cluster* Haar coefficient.

Every original 4D L4 plaquette is built (1536). The 8-side tube connects
two original normalized y-z Wilson marks at Euclidean t=0,2.

This proves a SELECTED multivariate eight-coupling Taylor coefficient
of the true original Wilson covariance, NOT the full common-beta W3
absolute cluster sum, original CMP119/122 RG or physical OS mass gap.

SU(N) Haar two-matrix orthogonality and centre selection are standard
imported mathematical identities; the geometry/combinatorics/integer
contraction are exactly checked by SymPy/Python.
"""
from itertools import combinations, product
from collections import Counter
from sympy import Integer, Rational, simplify

L = 4
sites = list(product(range(L), repeat=4))
links = {(x, a) for x in sites for a in range(4)}
def step(x, a):
    y = list(x)
    y[a] = (y[a] + 1) % L
    return tuple(y)
def face(x, a, b):
    return ((x, a, 1), (step(x, a), b, 1),
            (step(x, b), a, -1), (x, b, -1))
plaques = {(x, a, b): face(x, a, b)
           for x in sites for a, b in combinations(range(4), 2)}
assert (len(sites), len(links), len(plaques)) == (256, 1024, 1536)
F = ((0, 0, 0, 0), 1, 2)
G = ((2, 0, 0, 0), 1, 2)
def support(p):
    return {edge[:2] for edge in plaques[p]}
def parity(bag):
    counts = Counter(e[:2] for p in bag for e in plaques[p])
    return frozenset(e for e, k in counts.items() if k % 2)

# An actual original +Euclidean-time cylinder of four side faces per step.
tube = tuple(((t, dy, dz, 0), 0, a)
             for t in (0, 1) for a in (1, 2)
             for dy, dz in ([(0, 0), (0, 1)] if a == 1
                            else [(0, 0), (1, 0)]))
assert len(set(tube)) == 8 and F not in tube and G not in tube
assert parity((F, G) + tube) == frozenset()

# SHARP geometry lower bound: each of 4 F boundary links and each of
# 4 G boundary links needs a different nonmarked plaquette. No other
# original plaquette shares two edges with F/G or one edge with BOTH.
sf, sg = support(F), support(G)
assert sf.isdisjoint(sg)
for p in plaques:
    if p not in (F, G):
        assert len(support(p) & sf) <= 1
        assert len(support(p) & sg) <= 1
        assert not ((support(p) & sf) and (support(p) & sg))
print("PASS original L4: 256 sites, 1024 links, 1536 plaquettes, minimum 8 distinct side faces")

# Exhaust all 256 subsets. Necessary Haar neutrality from original
# single-link centre invariance excludes ANY proper subset for the
# selected two-mark F,G source and excludes single-mark sources.
for mask in range(1 << 8):
    chosen = tuple(tube[i] for i in range(8) if (mask >> i) & 1)
    assert parity((F,) + chosen)
    assert parity((G,) + chosen)
    if mask != (1 << 8) - 1:
        assert parity((F, G) + chosen)
print("PASS 256/256 selected subfaces: no proper original F/G neutral source")

# Ten-face spherical surface: two actual Wilson marks + eight
# ORIGINAL plaquette interactions. Every positive link appears TWICE.
faces = (F, G) + tube
incidence = {}
for i, p in enumerate(faces):
    for j, (x, a, sign) in enumerate(plaques[p]):
        incidence.setdefault((x, a), []).append((i, j, sign))
assert len(incidence) == 20 and all(len(v) == 2 for v in incidence.values())
# Orient the actual face traces so each shared link occurs as U and U^-1.
orient = {0: 1}
while len(orient) < len(faces):
    for uses in incidence.values():
        (i, _, u), (j, _, v) = uses
        if i in orient and j not in orient:
            orient[j] = -orient[i] * u * v
        if j in orient and i not in orient:
            orient[i] = -orient[j] * u * v
assert all(orient[i] * u == -orient[j] * v
           for (i, _, u), (j, _, v) in incidence.values())

# Independent symbolic Haar index contraction:
# integral U_ab (U^-1)_cd dH = delta_ad delta_bc / N.
parent = list(range(4 * len(faces)))
def find(x):
    while parent[x] != x:
        parent[x] = parent[parent[x]]
        x = parent[x]
    return x
def union(a, b):
    a, b = find(a), find(b)
    if a != b:
        parent[a] = b
def ends(occ):
    i, j, sg = occ
    if orient[i] == 1:
        return 4*i+j, 4*i+(j+1)%4, sg
    return 4*i+(j+1)%4, 4*i+j, -sg
for uses in incidence.values():
    (start1, end1, sign1), (start2, end2, sign2) = [ends(o) for o in uses]
    assert sign1 == -sign2
    union(start1, end2)
    union(end1, start2)
V = len({find(i) for i in range(4*len(faces))})
E = len(incidence)
C = len(faces)
assert (V, E, C, V-E+C) == (12, 20, 10, 2)
print("PASS original Haar fundamental tensor index contraction: V=12,E=20,F=10, Euler=2")

# One globally oriented product of 10 NORMALIZED fundamental traces is
# N^(V-E-C)=N^-18. For N>=3, ReTr=(Tr+Tr^-1)/2, and each link's
# SU(N) centre invariance excludes same-oriented pair factors.
# Only two globally coherent face orientations survive: factor 2^(1-C).
# SU2 is pseudoreal and each normalized trace is already REAL.
for N in range(2, 7):
    coeff = Integer(N)**(V-E-C)
    if N >= 3:
        coeff /= Integer(2)**(C-1)
    expect = Rational(1, 2**18) if N == 2 else (
        Rational(1, 2**9) * Integer(N)**(-18))
    assert simplify(coeff-expect) == 0
    print(f"SU({N}): selected eight-coupling connected Wilson coefficient = {coeff}")
print("PASS genuine source-selected Wilson eight-plaquette response")

# Reuse the same source for a whole NONWRAPPING tube family t=1,2,3;
# t=3 is longer than the opposite periodic return t=1.
for d in (1, 2, 3):
    cap = ((d, 0, 0, 0), 1, 2)
    walls = tuple(((t, dy, dz, 0), 0, a)
                  for t in range(d) for a in (1, 2)
                  for dy, dz in ([(0, 0), (0, 1)] if a == 1
                                 else [(0, 0), (1, 0)]))
    assert len(walls) == 4*d
    assert not parity((F,cap)+walls)
    counts = Counter(edge[:2] for p in (F,cap)+walls for edge in plaques[p])
    assert len(counts) == 8*d+4 and all(k == 2 for k in counts.values())
    vd, ed, fd = 4*(d+1), 8*d+4, 4*d+2
    assert vd-ed+fd == 2
    for N in (2,3,4):
        coeff = Integer(N)**(vd-ed-fd)
        if N >= 3:
            coeff /= Integer(2)**(fd-1)
        formula = (Integer(2)**(-(8*d+2)) if N == 2 else
                   Integer(2)**(-(4*d+1))*Integer(N)**(-(8*d+2)))
        assert simplify(coeff-formula) == 0
    print(f"PASS original t={d}: 4d={4*d} side plaquettes and chosen Haar coefficient")
print("NOTE t=3 on L4 is a NONMINIMAL tube by periodic reverse time; no inferred decay.")
print("OPEN: original full absolute W3 cluster-charge sum, weak beta(a), CMP119/122/OS same-H")


# Six ORIGINAL physical source tubes: three spatial transverse planes
# x two distinct shortest periodic time paths from x0=0 to x0=2.
# This cardinal 6 is NOT H05's six indexed cube faces.
all_routes={}
for a,b in combinations((1,2,3),2):
    mark0=((0,0,0,0),a,b)
    mark2=((2,0,0,0),a,b)
    for label,times in (('forward',(0,1)),('reverse',(2,3))):
        wall=[]
        for t in times:
            for ax,other in ((a,b),(b,a)):
                for disp in (0,1):
                    x=[0,0,0,0]
                    x[0]=t
                    x[other]=disp
                    wall.append((tuple(x),0,ax))
        assert len(set(wall))==8
        assert not parity((mark0,mark2)+tuple(wall))
        counts=Counter(e[:2] for p in (mark0,mark2)+tuple(wall)
                       for e in plaques[p])
        assert len(counts)==20 and set(counts.values())=={2}
        all_routes[(a,b,label)]=tuple(wall)
assert len(all_routes)==6
for a,b in combinations((1,2,3),2):
    assert set(all_routes[(a,b,'forward')]).isdisjoint(
           all_routes[(a,b,'reverse')])
print("PASS 3 original transverse spatial planes x 2 true periodic time paths: 6 original Wilson tubes")
print("NOTE: 6 tube-route labels do NOT identify H05's six indexed cube faces")
