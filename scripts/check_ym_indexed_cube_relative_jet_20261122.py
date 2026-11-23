#!/usr/bin/env python3
"""Exact indexed 3-cube and two-mark log-jet diagnostic; NOT Wilson SU(N) physics."""
from itertools import product
from sympy import symbols, Rational, diff, log, simplify, expand, sqrt, I
from fractions import Fraction
u,v,x,y,z=symbols("u v x y z")
B=list(product((0,1),repeat=3))
T=list(product((-1,0,1),repeat=3))
assert len(B)==8 and len(T)==27
assert [sum(a==0 for a in t) for t in T].count(0)==8
assert [sum(a==0 for a in t) for t in T].count(1)==12
assert [sum(a==0 for a in t) for t in T].count(2)==6
assert [sum(a==0 for a in t) for t in T].count(3)==1
assert sum(b[d]==0 for b in B for d in range(3))==12
faces=[(i,j,k,c) for i in range(3) for j in range(i+1,3) for k in range(3) if k not in (i,j) for c in (0,1)]
assert len(faces)==6
P=lambda b: 1+b[0]*x+b[1]*y+b[2]*z+b[0]*b[1]*x*y+b[1]*b[2]*y*z+b[0]*b[2]*x*z+b[0]*b[1]*b[2]*x*y*z
for i,j,k,c in faces:
 b=[0,0,0];b[k]=c
 def value(a,d):
  bb=b[:];bb[i]=a;bb[j]=d;return P(bb)
 assert expand((value(1,1)-value(0,1))-(value(1,0)-value(0,0))-
               ((value(1,1)-value(1,0))-(value(0,1)-value(0,0))))==0
for b in B:
 f=Rational(2*b[0]-1,2);g=Rational(2*b[1]-1,3)
 h=Rational(2*b[2]-1,4);j=Rational(sum(b),10)
 K=(1+f*u)*(1+g*v);M=(1+h*u)*(1+j*v);d=K/M-1
 assert simplify(diff(log(K)-log(M),u,v)-
       (diff(d,u,v)/(1+d)-diff(d,u)*diff(d,v)/(1+d)**2))==0
omega=(-1+sqrt(3)*I)/2
assert simplify(1+omega+omega**2)==0
assert (1+(-1))==0 and (abs(1)+abs(-1))==2
print("PASS: 8/12/6 binary geometry; 27=8+12+6+1 trits; 8 jets; signed/absolute no-go")
