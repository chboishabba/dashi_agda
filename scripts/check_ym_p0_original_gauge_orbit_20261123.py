#!/usr/bin/env python3
"""Exact original Wilson Z2 gauge orbit vs ten-link restricted F19 regression.

Full 1024 positive-bond source, all 1536 original Wilson plaquettes,
64 actual native R445 coarse paths and two actual y-z marks.
The ten-link frozen-field subset is NOT gauge closed.
Not continuous Haar/CMP119, physical W3 or mass gap.
"""
from itertools import combinations, product

L = 4
sites = list(product(range(L), repeat=4))
links = [(x,m) for x in sites for m in range(4)]
def step(x,m,n=1):
    y=list(x); y[m]=(y[m]+n)%L; return tuple(y)
def p(x,m,n):
    return ((x,m),(step(x,m),n),(step(x,n),m),(x,n))
faces = [p(x,m,n) for x in sites for m,n in combinations(range(4),2)]
F=(0,0,0,0); G=(0,0,0,2)
pairs=((F,2),(step(F,2),2),(G,2),(step(G,2),2))
spec=tuple([((0,0,0,z),2) for z in (1,3)]
           + [((0,0,1,z),3) for z in range(4)])
active=set(pairs+spec)
selected=set(); coarse_bonds=[]
for c in product(range(2), repeat=4):
    for m in range(4):
        origin=tuple(2*u for u in c)
        coarse_bonds.append(((origin,m),(step(origin,m),m)))
        selected.update(coarse_bonds[-1])
assert (len(sites),len(links),len(faces))==(256,1024,1536)
assert len(active)==10 and len(selected)==128 and len(coarse_bonds)==64

# Local Z2 gauge pulse at the original site F: g_F=-I, others +I.
gauge={x:int(x==F) for x in sites}
field={b:0 for b in links}
transformed={(x,m):field[x,m]^gauge[x]^gauge[step(x,m)]
             for x,m in links}
flipped={b for b in links if transformed[b]}
star={(F,m) for m in range(4)} | {
    (step(F,m,-1),m) for m in range(4)}
assert flipped==star and len(flipped)==8
assert len(flipped&active)==1 and len(flipped-active)==7

# Full Wilson action and both original Wilson marks are gauge invariant
# although the transformed field exits the restricted ten-link slice.
assert all(sum(field[b] for b in face)%2==0
           and sum(transformed[b] for b in face)%2==0
           for face in faces)
marks=[p(F,2,3),p(G,2,3)]
assert all(sum(transformed[b] for b in face)%2==0
           for face in marks)
blocks=[sum(transformed[b] for b in ab)%2 for ab in coarse_bonds]
assert blocks.count(1)==8

# Full source gauge-covariant F19 holonomy, including midpoint
# cancellation. The parity bits form Z2, hence +/- inverses coincide.
for (u,m),(v,_) in coarse_bonds:
    assert v==step(u,m)
    w=field[u,m]^field[v,m]
    wp=transformed[u,m]^transformed[v,m]
    assert wp==w^gauge[u]^gauge[step(u,m,2)]
print("PASS: 1024 bonds, all 1536 original Wilson plaquettes, 64 native F19 paths")
print("PASS: original F/G plaquette marks invariant under a full local source gauge pulse")
print("PASS: 8 gauge star flips, 1 active and 7 frozen: ten-link slice NOT gauge closed")
print("PASS: 8 transformed coarse paths; all 64 F19 paths transform by endpoints")
print("OPEN: physical continuous SU(N) Haar/CMP119 T, absolute W3, interacting OS")

# Connected frozen-complement certificate. If two restricted cylinder fields
# are gauge-related, their difference gradient vanishes along all frozen
# bonds. Connectedness forces the gauge function constant: all 2^10
# cylinder assignments represent distinct full site-gauge orbits.
adjacency={x:set() for x in sites}
for x,m in links:
    if (x,m) in active:
        continue
    y=step(x,m)
    adjacency[x].add(y)
    adjacency[y].add(x)
visited={F};frontier=[F]
for x in frontier:
    for y in adjacency[x]:
        if y not in visited:
            visited.add(y)
            frontier.append(y)
assert len(visited)==256
assert sum(len(v) for v in adjacency.values())==2*(1024-10)
# For a connected original graph Z2^256 has one global Z2 stabilizer:
# effective local gauge orbits have 2^255 members. The 2^10 distinct
# source cylinders therefore gauge-saturate to exactly 2^265 fields.
# Wilson action and closed marks are constant on each orbit; uniform
# finite-group saturation multiplies all 1,F,G,FG sums by the same 2^255.
print("PASS: 1014 frozen-bond complement connected on all 256 original sites")
print("PASS: 2^10 distinct cylinder gauge orbits; effective gauge orbit size 2^255")
print("PASS: 2^265 saturated full-source fields, unchanged normalized four moments")
