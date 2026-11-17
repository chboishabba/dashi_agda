#!/usr/bin/env python3
"""Literal original 4D periodic SU2 Wilson polynomial -> rational moment.

At side L, enumerates 4L^4 independent positive-link unit-quaternion
variables and 6L^4 original positive-plane plaquette words, with
quaternion inverses represented by conjugates on the unit sphere.
Integrates arbitrary coordinate polynomials by Pochhammer moments,
linkwise. No numerical quadrature or invented Haar authority. High
Taylor orders may be exponentially expensive; use incidence/sparse
certificates for those. Does not claim Agda kernel acceptance.
Attribution: Wilson/Balaban, Pizzetti/Folland, original DASHI bonds.
"""
from fractions import Fraction as Q
from itertools import product,combinations
from functools import lru_cache
from math import prod
import argparse

@lru_cache(None)
def poch(a,n):
 p=Q(1)
 for j in range(n):p*=a+j
 return p

def moment(e):
 if any(n%2 for n in e):return Q(0)
 a=[n//2 for n in e]
 return prod(poch(Q(1,2),z) for z in a)/poch(Q(2),sum(a))

class PolynomialRing:
 def __init__(self,n):
  self.n=n;self.zero=(0,)*(4*n)
 def constant(self,c):return {self.zero:Q(c)} if c else {}
 def variable(self,link,component):
  e=list(self.zero);e[4*link+component]=1
  return {tuple(e):Q(1)}
 def add(self,A,B):
  out=A.copy()
  for e,c in B.items():out[e]=out.get(e,Q(0))+c
  return {e:c for e,c in out.items() if c}
 def neg(self,A):return {e:-c for e,c in A.items()}
 def sub(self,A,B):return self.add(A,self.neg(B))
 def mul(self,A,B):
  if len(A)>len(B):A,B=B,A
  out={}
  for e,c in A.items():
   for f,d in B.items():
    g=tuple(x+y for x,y in zip(e,f))
    out[g]=out.get(g,Q(0))+c*d
  return {e:c for e,c in out.items() if c}
 def integral(self,A):
  result=Q(0)
  for e,c in A.items():
   v=c
   for j in range(self.n):
    v*=moment(e[4*j:4*j+4])
    if not v:break
   result+=v
  return result
 def quat(self,a,b):
  m=self.mul;add=self.add;sub=self.sub
  p,q,r,s=a;t,u,v,w=b
  return (sub(sub(sub(m(p,t),m(q,u)),m(r,v)),m(s,w)),
          sub(add(add(m(p,u),m(q,t)),m(r,w)),m(s,v)),
          add(sub(add(m(p,v),m(r,t)),m(q,w)),m(s,u)),
          add(sub(add(m(p,w),m(s,t)),m(r,u)),m(q,v)))
 def conj(self,q):return (q[0],self.neg(q[1]),self.neg(q[2]),self.neg(q[3]))

def original_source(L):
 assert L>=1
 sites=list(product(range(L),repeat=4))
 ids={(x,a):i for i,(x,a) in enumerate(
      (x,a) for x in sites for a in range(4))}
 ring=PolynomialRing(len(ids))
 def step(x,a):
  y=list(x);y[a]=(y[a]+1)%L
  return tuple(y)
 def link(x,a):
  k=ids[(x,a)]
  return tuple(ring.variable(k,c) for c in range(4))
 def trace(x,a,b):
  # Native positive-oriented plaquette U_a(x) U_b(x+ea)
  # U_a(x+eb)^-1 U_b(x)^-1; conjugate = inverse on S3.
  p=ring.quat(link(x,a),link(step(x,a),b))
  p=ring.quat(p,ring.conj(link(step(x,b),a)))
  p=ring.quat(p,ring.conj(link(x,b)))
  return p[0]
 D=ring.constant(6*L**4)
 for x in sites:
  for a,b in combinations(range(4),2):
   D=ring.sub(D,trace(x,a,b))
 return ring,D

def run(L,order):
 ring,D=original_source(L)
 print(f"side={L}, links={ring.n}, plaquettes={6*L**4}, "
       f"deficit_monomials={len(D)}")
 poly=ring.constant(1)
 for k in range(order+1):
  value=ring.integral(poly)
  print(f"k={k} terms={len(poly)} exact_H[D^k]={value}")
  if L==1 and k<=2:
   assert value==(Q(1),Q(9,2),Q(187,8))[k]
  if L>=2 and k<=1:
   assert value==(Q(1),Q(6*L**4))[k]
  if k<order:poly=ring.mul(poly,D)
 print("ORIGINAL_PERIODIC_WILSON_CYLINDER_COMPILER_PASS")

if __name__=="__main__":
 parser=argparse.ArgumentParser()
 parser.add_argument("--side",type=int,default=1)
 parser.add_argument("--order",type=int,default=2)
 args=parser.parse_args()
 run(args.side,args.order)
