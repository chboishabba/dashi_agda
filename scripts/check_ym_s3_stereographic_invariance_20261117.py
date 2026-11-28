#!/usr/bin/env python3
"""Exact Q(t) S3 stereographic weighted-divergence and all-degree moments.

phi(t)=((1-r²)/(1+r²),2t/(1+r²)),
J(t)=8/(1+r²)^3. For each of the three rotations mixing q0,qi,
V_i=(1-r²)/2 e_i + t_i t, and div(J V_i)=0.
This rational identity + vanishing boundary flux proves invariant
integral of P(phi), hence the moment recurrence, without pi,
sin/cos or square roots. Integration-by-parts needs native Agda proof.
"""
import sympy as s
from fractions import Fraction as F

x,y,z=s.symbols('x y z',real=True)
t=s.Matrix([x,y,z]);r=t.dot(t);d=1+r
phi=s.Matrix([(1-r)/d]+[2*v/d for v in t]);J=8/d**3
checks=0
def eq(a,b,tag):
 global checks
 assert s.cancel(a-b)==0,tag
 checks+=1

for i in range(3):
 V=s.Matrix([(1-r)/2*(1 if j==i else 0)+t[i]*t[j]
             for j in range(3)])
 eq(sum(s.diff(J*V[j],t[j]) for j in range(3)),0,'divergence')
 for a in range(4):
  lhs=sum(V[j]*s.diff(phi[a],t[j]) for j in range(3))
  rhs=-phi[i+1] if a==0 else (phi[0] if a==i+1 else 0)
  eq(lhs,rhs,'rotation generator')
 eq(sum(s.diff(V[j],t[j]) for j in range(3)),3*t[i],'div V')
 eq(sum(t[j]*V[j] for j in range(3)),t[i]*d/2,'tV')
for i in range(3):
 subs={t[i]:-t[i]}
 eq(J.subs(subs),J,'reflection J')
 for j in range(4):
  eq(phi[j].subs(subs),-phi[j] if j==i+1 else phi[j],'reflection phi')

def poch(a,n):
 v=F(1)
 for j in range(n):v*=a+j
 return v
def H(exponents):
 if any(k%2 for k in exponents):return F(0)
 a=[k//2 for k in exponents]
 return s.prod(poch(F(1,2),j) for j in a)/poch(F(2),sum(a))

for k in range(1,9):
 for a in range(k+1):
  for b in range(k-a+1):
   for c in range(k-a-b+1):
    e=k-a-b-c
    ex=[a,b,c,e]
    for i in range(4):
     if ex[i]==0:continue
     lower=ex.copy();lower[i]-=1
     assert H(tuple(2*v for v in ex))==F(2*ex[i]-1,2*(k+1))*H(tuple(2*v for v in lower))
     checks+=1
print('S3_STEREOGRAPHIC_INVARIANT_MOMENTS_PASS',checks)
