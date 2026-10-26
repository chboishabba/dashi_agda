#!/usr/bin/env python3
"""Exact signed-permutation crystal symmetry certificate.

Classical prior art: tetragonal holohedry 4/mmm and cubic m-3m,
and integral direct/reciprocal lattice duality (IUCr/Coxeter).
This is a finite exact certificate, not experimental crystallography.
"""
from itertools import permutations, product
from collections import Counter

I = ((1,0,0),(0,1,0),(0,0,1))
R = ((0,-1,0),(1,0,0),(0,0,1))
V = ((1,0,0),(0,-1,0),(0,0,1))
H = ((1,0,0),(0,1,0),(0,0,-1))

def mm(a,b):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(3))
                       for j in range(3)) for i in range(3))
def tp(a):
    return tuple(tuple(a[j][i] for j in range(3)) for i in range(3))
def power(a,n):
    p=I
    for _ in range(n):
        p=mm(p,a)
    return p

def mv(g,v):
    return tuple(sum(g[i][j]*v[j] for j in range(3)) for i in range(3))
def dot(p,q): return sum(x*y for x,y in zip(p,q))
def weighted(p,q,a,c):
    return a*(p[0]*q[0]+p[1]*q[1])+c*p[2]*q[2]
def signperm(perm,sign):
    return tuple(tuple(sign[i] if perm[i] == j else 0
                       for j in range(3)) for i in range(3))

D4h = {mm(mm(power(R,n),power(V,v)),power(H,h))
       for n,v,h in product(range(4),range(2),range(2))}
B3 = {signperm(perm,sign) for perm in permutations(range(3))
      for sign in product((-1,1),repeat=3)}
assert len(D4h)==16 and len(B3)==48 and D4h<=B3
assert {mm(g,h) for g in D4h for h in D4h} == D4h
assert {mm(g,h) for g in B3 for h in B3} == B3
assert all(mm(tp(g),g)==I for g in B3)

# Symbolic diagonal metric coefficients represented as coefficient pairs:
# a=(1,0), c=(0,1).  No numerical sample is substituted into this test.
a=(1,0)
c=(0,1)
zero=(0,0)
M=((a,zero,zero),(zero,a,zero),(zero,zero,c))
def mul_coeff(m,g):
    return tuple(tuple(tuple(sum(m[i][k][t]*g[k][j] for k in range(3))
                              for t in range(2))
                       for j in range(3)) for i in range(3))
def mul_left(g,m):
    return tuple(tuple(tuple(sum(g[i][k]*m[k][j][t] for k in range(3))
                              for t in range(2))
                       for j in range(3)) for i in range(3))
tetragonal={g for g in B3 if mul_left(tp(g),mul_coeff(M,g)) == M}
assert tetragonal==D4h

# When a=c, all 48 preserve the cubic Euclidean form.
assert all(mm(tp(g),g)==I for g in B3)

vectors=list(product((-1,0,1),repeat=3))
for g in B3:
    for p,q in product(vectors,repeat=2):
        # Orthogonal integral signed permutation -> U^{-T}=U.
        assert dot(mv(g,p),mv(g,q))==dot(p,q)
        assert mv(g,tuple(x+y for x,y in zip(p,q))) ==                tuple(x+y for x,y in zip(mv(g,p),mv(g,q)))
for g in D4h:
    for p,q in product(vectors,repeat=2):
        assert weighted(mv(g,p),mv(g,q),2,7)==weighted(p,q,2,7)

print("PASS: B3 cubic 48 and D4h tetragonal 16 closed integral actions")
print("PASS: symbolic generic diag(a,a,c) stabilizer in B3 exactly D4h")
print("PASS: cubic a=c enhancement to all B3; Fourier pairing and additivity")
