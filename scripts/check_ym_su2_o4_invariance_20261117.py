#!/usr/bin/env python3
"""Exact S3 O(4) moment tensor and rational rotation certificate.

For 2k coordinates:
 H(q_i1...q_i2k) =
 [sum over pairings product_{pairs} delta_ij]/[4*6*...*(2k+2)].
The tensor expression is O(4) invariant in every degree by contraction.
Numerical checks here use exact rationals; no Haar axiom or Agda proof.
Attribution: Pizzetti/Folland and original DASHI SU2 moment sources.
"""
from fractions import Fraction as F
from functools import lru_cache
import sympy as sp

checks=0
def poch(x,n):
 out=F(1)
 for j in range(n):out*=x+j
 return out
def sphere(e):
 if any(k%2 for k in e):return F(0)
 a=[k//2 for k in e]
 out=F(1)
 for k in a:out*=poch(F(1,2),k)
 return out/poch(F(2),sum(a))
def monomials(d):
 for a in range(d+1):
  for b in range(d+1-a):
   for c in range(d+1-a-b):
    for e in range(d+1-a-b-c):yield a,b,c,e
@lru_cache(None)
def pairings(indices):
 if not indices:return 1
 first=indices[0]
 return sum(pairings(indices[1:j]+indices[j+1:])
            for j in range(1,len(indices)) if indices[j]==first)
def tensor_moment(e):
 degree=sum(e)
 if degree%2:return F(0)
 indices=tuple(i for i,k in enumerate(e) for _ in range(k))
 denom=1
 for k in range(degree//2):denom*=4+2*k
 return F(pairings(indices),denom)

for e in monomials(10):
 assert tensor_moment(e)==sphere(e),e
 checks+=1
q=sp.symbols('q0:4')
O=sp.eye(4)
O[0,0]=sp.Rational(3,5);O[0,1]=-sp.Rational(4,5)
O[1,0]=sp.Rational(4,5);O[1,1]=sp.Rational(3,5)
assert O.T*O==sp.eye(4)
checks+=1
Q=list(O*sp.Matrix(q))
def H(poly):
 p=sp.Poly(sp.expand(poly),*q,domain=sp.QQ)
 return sum((coeff*sphere(e) for e,coeff in p.terms()),sp.Rational(0))
for e in monomials(6):
 lhs=H(sp.prod(q[i]**e[i] for i in range(4)))
 rhs=H(sp.prod(Q[i]**e[i] for i in range(4)))
 assert lhs==rhs,(e,lhs,rhs)
 checks+=1
print("YM_REAL_O4_TENSOR_AND_RATIONAL_ROTATION_PASS",checks)
