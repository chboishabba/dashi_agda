#!/usr/bin/env python3
"""Exact rational Reynolds and character fingerprints for classical D4h.

Attribution: classical finite-group representation theory (Maschke/Reynolds);
DASHI implementation reuses mathematical strategy from the C3 projector in
PR #1244. This script does not prove any measured crystal space group.
"""
from fractions import Fraction as Q
from itertools import product

G=list(product(range(4),range(2),range(2)))
def mul(g,h):
 a,b,c=g; d,e,f=h
 return ((a+(-d if b else d))%4,b^e,c^f)
def matmul(a,b):
 return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(3)) for j in range(3)) for i in range(3))
I=((1,0,0),(0,1,0),(0,0,1))
R=((0,-1,0),(1,0,0),(0,0,1))
S=((1,0,0),(0,-1,0),(0,0,1))
H=((1,0,0),(0,1,0),(0,0,-1))
def power(m,n):
 a=I
 for _ in range(n):a=matmul(a,m)
 return a
def matrix(g):
 a,b,c=g
 return matmul(matmul(power(R,a),power(S,b)),power(H,c))
def reynolds():
 # Average the natural three-dimensional representation on Q^3:
 # constant projector equals zero since both xy and z sign flips occur.
 return tuple(tuple(sum(Q(matrix(g)[i][j],16) for g in G)
                    for j in range(3)) for i in range(3))
def rank2(m):
 return tuple(tuple(sum(Q(m[i][k])*m[k][j] for k in range(3))
                    for j in range(3)) for i in range(3))
def check():
 zero=((Q(0),)*3,)*3
 assert reynolds()==zero
 # projector for symmetric rank-two diagonal tensors:
 # action conjugation T -> g T g^t gives isotropic xy and separate z.
 def trans(a):return tuple(zip(*a))
 def avg(T):
  return tuple(tuple(sum(Q(matmul(matmul(matrix(g),T),trans(matrix(g)))[i][j],16)
                         for g in G) for j in range(3)) for i in range(3))
 X=((1,0,0),(0,0,0),(0,0,0))
 Z=((0,0,0),(0,0,0),(0,0,1))
 assert avg(X)==((Q(1,2),0,0),(0,Q(1,2),0),(0,0,0))
 assert avg(Z)==Z
 for g in G:
  assert avg(matmul(matmul(matrix(g),X),trans(matrix(g))))==avg(X)
 print("PASS: 3D Reynolds projector zero; quadratic tensors split xy/z; equivariance.")
if __name__=="__main__":check()
