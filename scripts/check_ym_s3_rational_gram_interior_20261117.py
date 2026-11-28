#!/usr/bin/env python3
"""Exact rational S3 Gram coercivity for finite-degree design search.

Filtered rational basis uses q0 powers only 0 or 1, reducing by
q0²=1-q1²-q2²-q3². Gram_ij=H(b_i b_j) from exact Pochhammer.
Exact LDL rational positivity, determinant, trace, and explicit
det/(trace)^(dim-1) rational eigenvalue lower bound.
No numerical spectrum, pi, roots or Haar positivity postulate.
"""
from math import comb
import sympy as s
def H(e):
 if any(v%2 for v in e):return s.S(0)
 out=s.S(1);k=sum(e)//2
 for v in e:
  for j in range(v//2):out*=s.Rational(2*j+1,2)
 for j in range(k):out/=j+2
 return out
def basis(d):
 return [(a0,a1,a2,a3) for a0 in (0,1) if a0<=d
         for a1 in range(d-a0+1)
         for a2 in range(d-a0-a1+1)
         for a3 in range(d-a0-a1-a2+1)]
for d in range(4):
 b=basis(d);m=len(b)
 assert m==comb(d+3,3)+(comb(d+2,3) if d>=1 else 0)
 G=s.Matrix(m,m,lambda i,j:H(tuple(b[i][k]+b[j][k] for k in range(4))))
 D=G.LDLdecomposition(hermitian=False)[1]
 assert all(D[i,i]>0 for i in range(m))
 det=s.prod(D[i,i] for i in range(m))
 tr=s.trace(G)
 margin=det/tr**(m-1)
 assert margin>0
 print(f"degree={d}, dimension={m}, rational_margin={margin}")
print("YM_S3_RATIONAL_GRAM_INTERIOR_PASS")
