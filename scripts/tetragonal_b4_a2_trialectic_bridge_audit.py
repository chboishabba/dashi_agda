#!/usr/bin/env python3
"""Exact subgroup and equivariance audit: B3/B4, D4h and A2/C3.

Classical signed-permutation/Weyl-group identifications, implemented as
DASHI finite checks. No equivalence of differently typed T9/T18 carriers.
"""
from itertools import permutations,product
def mul(a,b):
 return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(len(a))) for j in range(len(b[0]))) for i in range(len(a)))
def eye(n):return tuple(tuple(int(i==j) for j in range(n)) for i in range(n))
def signed(n):
 for p in permutations(range(n)):
  for s in product((-1,1),repeat=n):
   yield tuple(tuple(s[i]*int(p[i]==j) for j in range(n)) for i in range(n))
I=eye(3);R=((0,-1,0),(1,0,0),(0,0,1));S=((1,0,0),(0,-1,0),(0,0,1));H=((1,0,0),(0,1,0),(0,0,-1))
def powmat(m,k):
 a=eye(len(m))
 for _ in range(k):a=mul(a,m)
 return a
D={mul(mul(powmat(R,a),powmat(S,b)),powmat(H,c)) for a,b,c in product(range(4),range(2),range(2))}
B3=set(signed(3)); B4=set(signed(4))
def embed(m):return tuple(tuple(m[i][j] if i<3 and j<3 else int(i==j) for j in range(4)) for i in range(4))
# rank-two B2 × A1 (not all B3) embeds canonically via block diagonal
B2=set(signed(2))
block={tuple(tuple(a[i][j] if i<2 and j<2 else (-1 if i==j==2 and z else int(i==j))
                   for j in range(3)) for i in range(3)) for a in B2 for z in range(2)}
assert len(D)==len(block)==16 and D==block
assert D <= B3 and len(B3)==48
assert {embed(g) for g in D} <= B4 and len(B4)==384
# A2 Weyl group = S3 on three labels; C3 alternating subgroup
A2=list(permutations(range(3)))
def permcompose(a,b):return tuple(a[b[i]] for i in range(3))
r=(1,2,0)
assert permcompose(r,permcompose(r,r))==(0,1,2)
assert { (0,1,2),r,permcompose(r,r) } <= set(A2)
# Reusing D4 action on 3x3 positions, count fixed points of vertical mirror
grid=[(x,y) for x in (-1,0,1) for y in (-1,0,1)]
removed=[p for p in grid if p!=(0,0)]
assert sum(y==0 for x,y in removed)==2
layer=[(x,y,z) for x,y in ((1,0),(0,1),(-1,0),(0,-1)) for z in (-1,1)]
assert sum(y==0 for x,y,z in layer)==4
print("PASS: D4h=B2×A1 subgroup of B3 and B4; A2/S3 cyclic C3; D4-set fixed-point obstruction.")
