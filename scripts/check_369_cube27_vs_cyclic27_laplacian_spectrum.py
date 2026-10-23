#!/usr/bin/env python3
"""Independent exact dashiQ spectral discriminator for two 27-element carriers.

Cube27: Cartesian P3 x P3 x P3, geometric nearest-neighbour edges.
Cyclic27: Cayley graph of Z/27 with +/-1 neighbours.
They are equally sized SETS but have provably different coupling graphs
and Laplacian spectra. These are candidate physical observable predictions
ONLY if an actual Hamiltonian/diffusion operator realises the named edges.
"""
from collections import Counter
from itertools import product
import sympy as s

P=s.Matrix([[1,-1,0],[-1,2,-1],[0,-1,1]])
I=s.eye(3)
Lc=s.kronecker_product(P,I,I)+s.kronecker_product(I,P,I)+s.kronecker_product(I,I,P)
assert Lc.shape==(27,27) and Lc==Lc.T
assert all(sum(Lc[i,j] for j in range(27))==0 for i in range(27))
expected=Counter(sum(x) for x in product((0,1,3),repeat=3))
assert expected==Counter({0:1,1:3,2:3,3:4,4:6,5:3,6:3,7:3,9:1})
lam=s.Symbol('lam')
characteristic=s.factor(Lc.charpoly(lam).as_expr())
assert s.expand(characteristic-
    s.prod((lam-e)**count for e,count in expected.items()))==0
assert s.trace(Lc)==108 and s.trace(Lc*Lc)==558

Lcycle=2*s.eye(27)
for i in range(27):
    Lcycle[i,(i+1)%27]-=1
    Lcycle[i,(i-1)%27]-=1
assert Lcycle==Lcycle.T
assert all(sum(Lcycle[i,j] for j in range(27))==0 for i in range(27))
assert s.trace(Lcycle)==54 and s.trace(Lcycle*Lcycle)==162
assert Lc.charpoly(lam).as_expr()!=Lcycle.charpoly(lam).as_expr()
assert sorted(set(int(Lc[i,i]) for i in range(27)))==[3,4,5,6]
assert all(Lcycle[i,i]==2 for i in range(27))
print('PASS geometry Cube27 P3^3 spectrum:', sorted(expected.items()))
print('PASS Cube27 graph-Laplacian charpoly:',characteristic)
print('PASS Cube27 traces (L,L^2)=(108,558)')
print('PASS cyclic Z/27 traces (L,L^2)=(54,162), non-isospectral')
print('CONDITIONAL OBSERVABLE: requires adjacency-coupled dynamics calibrated on same source')
print('NO Monster-VOA/KK physical identity follows from distinct finite spectra')
