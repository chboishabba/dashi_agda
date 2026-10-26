#!/usr/bin/env python3
"""Finite integer certificate for classical tetragonal D4h on Z^3."""
from itertools import product
I=((1,0,0),(0,1,0),(0,0,1))
R=((0,-1,0),(1,0,0),(0,0,1))
V=((1,0,0),(0,-1,0),(0,0,1))
H=((1,0,0),(0,1,0),(0,0,-1))
def mul(a,b):
 return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(3)) for j in range(3)) for i in range(3))
def transpose(a):return tuple(zip(*a))
def power(a,n):
 x=I
 for _ in range(n):x=mul(x,a)
 return x
G={mul(mul(power(R,a),power(V,b)),power(H,c)) for a,b,c in product(range(4),range(2),range(2))}
assert len(G)==16
def mv(g,x):return tuple(sum(g[i][j]*x[j] for j in range(3)) for i in range(3))
def dot(x,y):return sum(a*b for a,b in zip(x,y))
for a,c in product((1,2,5),(1,3,7)):
 M=((a,0,0),(0,a,0),(0,0,c))
 for g in G:
  assert mul(mul(transpose(g),M),g)==M
  assert mul(transpose(g),g)==I
  for x in product(range(-2,3),repeat=3):
   for k in product(range(-2,3),repeat=3):
    assert dot(mv(g,x),mv(g,k))==dot(x,k)
print("PASS 16 integral D4h matrices: metric and reciprocal pairing invariance.")
