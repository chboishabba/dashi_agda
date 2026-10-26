#!/usr/bin/env python3
"""Exact finite audit of the native signed 27-cube, puncture, 13 axes, B3.

Distinct structures: nonwrapping cube graph, quotient by antipode,
signed permutation group, 8+9+9 z-sheets, binary orientation residual.
No claim about physical NV spin-level permutations or Agda kernel receipt.
"""
from itertools import product, permutations
from collections import Counter
T=(-1,0,1)
X=list(product(T, repeat=3))
O=(0,0,0)
punctured=[x for x in X if x!=O]
assert len(X)==27 and len(punctured)==26

def canonical(p):
    return min(p,tuple(-v for v in p))
axes={canonical(p) for p in punctured}
assert len(axes)==13
def support(p):return sum(v!=0 for v in p)
assert Counter(support(a) for a in axes)=={1:3,2:6,3:4}
assert Counter(p[2] for p in punctured)=={-1:9,0:8,1:9}
corner_axes={a for a in axes if support(a)==3}
assert len(corner_axes)==4
def adjacency(x,y):return sum(abs(a-b) for a,b in zip(x,y))==1
def act(g,p):
    perm,signs=g
    return tuple(signs[i]*p[perm[i]] for i in range(3))
G=list(product(permutations(range(3)),product((-1,1),repeat=3)))
assert len(G)==48
for g in G:
    assert {act(g,p) for p in X}==set(X)
    assert {canonical(act(g,p)) for p in punctured}==axes
    assert {canonical(act(g,p)) for p in corner_axes}==corner_axes
    assert all(adjacency(x,y)==adjacency(act(g,x),act(g,y)) for x in X for y in X)
kernel13=[g for g in G if all(canonical(act(g,a))==a for a in axes)]
kernel4=[g for g in G if all(canonical(act(g,a))==a for a in corner_axes)]
assert len(kernel13)==2 and len(kernel4)==2
assert {g[0] for g in kernel13}=={(0,1,2)}
assert {g[1] for g in kernel13}=={(1,1,1),(-1,-1,-1)}
assert {g[0] for g in kernel4}=={(0,1,2)}
assert {g[1] for g in kernel4}=={(1,1,1),(-1,-1,-1)}

# Quotient/residual is bijective: every nonzero p is a unique
# (unoriented axis, choice of one of two signs).
def encode(p):
    a=canonical(p)
    return a, int(p!=a)
def decode(a,flip):
    return tuple(-v for v in a) if flip else a
assert all(decode(*encode(p))==p for p in punctured)
assert all(encode(decode(a,b))==(a,b) for a in axes for b in (0,1))
# W(B3) induced action requires a residual cocycle / sign correction:
for g in G:
    for a in axes:
        base=act(g,a)
        dest=canonical(base)
        epsilon=int(base!=dest)
        for bit in (0,1):
            assert encode(act(g,decode(a,bit)))==(dest,bit^epsilon)
print("PASS: 27 native sites; punctured 8+9+9; 13=3+6+4 axes;")
print("PASS: B3=48 graph automorphisms; both 13-axis and four-axis kernels ±I; faithful oriented action;")
print("PASS: exact 26 ↔ 13×2 sign residual and equivariant XOR cocycle (48×13×2).")


# Actual P3^3 nonwrapping punctured graph: 26 vertices and 48 edges
# (six original origin-incident edges are REMOVED, not glued).
punctured_edges={frozenset((a,b)) for a,b in product(punctured,repeat=2)
                if a!=b and adjacency(a,b)}
assert len(punctured_edges)==48

# The 13 unoriented projective axes form a quotient GRAPH. Retain a
# signed Z2 orientation residual. This graph is NOT the PG(2,3)
# point-line incidence bipartite graph with 52 flags.
axis_edges={frozenset((a,b)) for a,b in product(axes,repeat=2)
            if a!=b and (adjacency(a,b) or adjacency(a,tuple(-v for v in b)))}
assert len(axis_edges)==24
assert Counter(sum(frozenset((a,b)) in axis_edges for b in axes if b!=a)
               for a in axes)=={4:9,3:4}
assert Counter(tuple(sorted((support(a),support(b)))) for a,b in
               (tuple(e) for e in axis_edges))=={(1,2):12,(2,3):12}

def edge_sign(a,b):
    assert frozenset((a,b)) in axis_edges
    yes=adjacency(a,b)
    flipped=adjacency(a,tuple(-v for v in b))
    assert yes != flipped
    return int(flipped)

# A four-cycle returns to the SAME projective axis but with the
# OPPOSITE orientation: XOR monodromy = 1, so a global graph-edge
# compatible orientation choice is mathematically impossible.
qcycle=[canonical(a) for a in
        ((1,0,0),(1,1,0),(0,1,0),(1,-1,0),(1,0,0))]
assert len(set(qcycle[:-1]))==4 and qcycle[0]==qcycle[-1]
assert all(frozenset((a,b)) in axis_edges for a,b in zip(qcycle,qcycle[1:]))
assert sum(edge_sign(a,b) for a,b in zip(qcycle,qcycle[1:]))%2==1

# Same projective 13 points also underlie PG(2,3), but that carries
# a DISTINCT 13x13 point-line incidence relation.
assert sum(sum(x*y for x,y in zip(a,b))%3==0 for a,b in
           product(axes,repeat=2))==52
print('PASS: original punctured P3^3 quotient graph 13 vertices/24 edges and support 12+12')
print('PASS: orientation XOR cocycle has explicit four-cycle odd holonomy; no global edge section')
print('BOUNDARY: PG(2,3) 52 incidence flags are distinct from 24 spatial quotient edges')
