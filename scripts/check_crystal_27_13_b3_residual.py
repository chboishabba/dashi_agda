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
assert {g[0] for g in kernel13}=={(0,1,2)}\nassert {g[1] for g in kernel13}=={(1,1,1),(-1,-1,-1)}\nassert {g[0] for g in kernel4}=={(0,1,2)}
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
