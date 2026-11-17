#!/usr/bin/env python3
"""Original Cube27 path operator vs chosen origin+26 Albert-shaped basis.
Exact finite checks, with clearly conditional real F4 irreducibility argument.
This is not a 27D string sigma-model or an F4 representation constructor.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import product

S = tuple(product((-1, 0, 1), repeat=3))
o = (0, 0, 0)
N = tuple(p for p in S if p != o)
assert len(N) == 26

def adj(p):
    for i in range(3):
        for d in (-1, 1):
            q = list(p)
            q[i] += d
            if -1 <= q[i] <= 1:
                yield tuple(q)

def L(f):
    return {p: sum((f[p] - f[q] for q in adj(p)), Q(0)) for p in S}

def delta(p):
    return {q: Q(int(p==q)) for q in S}

def gzero(f):
    mean = sum(f.values(), Q(0))/27
    return {p: f[p]-mean for p in S}

def quot(f):
    return {p: f[p]-f[o] for p in N}

def lift(a):
    s = -sum(a.values(), Q(0))/27
    return {p: s+(a[p] if p != o else Q(0)) for p in S}

def A(a):
    return quot(L(lift(a)))

def G(a,b):
    return (sum((a[x]*b[x] for x in N), Q(0))
            -sum(a.values(), Q(0))*sum(b.values(), Q(0))/27)

def vec26(p):
    return {x: Q(int(x==p)) for x in N}

v = L(delta(o))
assert v[o] == 6 and sum(x == -1 for p,x in v.items() if p!=o) == 6
assert sum(v.values(), Q(0)) == 0
print('PASS distinguished origin delta: L delta_o = 6 delta_o - six neighbor deltas')
print('NO-GO chosen origin scalar line is not L-invariant')

p = (1,0,0)
z = L(delta(p))
assert z[o] == -1
print('NO-GO 26 non-origin site basis is not L-invariant (delta_neighbor leaks -1 into origin)')

for a in map(vec26,N):
    la = lift(a)
    assert sum(la.values(), Q(0)) == 0
    assert quot(la) == a
    assert quot(L(la)) == A(a)
    for b in map(vec26,N):
        assert G(a,A(b)) == G(A(a),b)
print('PASS 26-dimensional zero-mean quotient, A selfadjoint in G: all 676 basis pairings')

modes = ((1,1,1),(1,0,-1),(1,-2,1))
lam = (0,1,3)
spec = Counter()
parity=Counter()
for ks in product(range(3),repeat=3):
    wave = {p:Q(modes[ks[0]][p[0]+1]*modes[ks[1]][p[1]+1]*modes[ks[2]][p[2]+1]) for p in S}
    eigen = sum(lam[j] for j in ks)
    assert L(wave)=={p:eigen*wave[p] for p in S}
    spec[eigen]+=1
    s = (-1)**sum(j==1 for j in ks)
    assert all(wave[tuple(-z for z in p)]==s*wave[p] for p in S)
    if ks!=(0,0,0):
        assert sum(wave.values())==0
        parity[s]+=1
assert spec == Counter({0:1,1:3,2:3,3:4,4:6,5:3,6:3,7:3,9:1})
assert parity==Counter({1:13,-1:13})
assert len(spec)-1==8
print('PASS nonconstant L eigenvalues/multiplicities',dict(sorted(spec.items())))
print('PASS parity of 26-mode spectral space: 13 even + 13 odd')
print('NO-GO L_nonconstant nonscalar (8 distinct positive eigenvalues)')
print('CONDITIONAL F4 no-go: on a real irreducible 26D F4-module, a selfadjoint F4-equivariant L is scalar')
print('CONDITIONAL thus no simultaneous F4-irreducibility + exact P3^3 L equivariance via isometry/intertwiner')

assert sum((Q(1) for p in S),Q(0)) == 27
assert L({p:Q(1) for p in S})=={p:Q(0) for p in S}
assert G({p:Q(1) for p in N},{p:Q(1) for p in N})==Q(26,27)
assert Q(125,121)!=1
print('PASS string coefficient ADVERSARY: literal Lambert-West 125/121 != 1 (imported source assertion, not action derived)')
print('BOUNDARY: no 27D gravity+3form reduction, K27 symmetry, Jordan product, Lorentz spacetime or BRST constructed')
