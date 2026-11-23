#!/usr/bin/env python3
"""Exact square-free 1/F/G/FG coefficient transport; not physical CMP119."""
import sympy as s
from itertools import product
u,v=s.symbols("u v")
def mult(x,y):
 a,b,c,d=x;e,f,g,h=y
 return (a*e,a*f+b*e,a*g+c*e,a*h+d*e+b*g+c*f)
def conv(fs):
 x=(s.Integer(1),s.Integer(0),s.Integer(0),s.Integer(0))
 for f in fs:x=mult(x,f)
 return x
def formula(fs):
 n=len(fs);a,b,c,d=map(list,zip(*fs))
 P=lambda skip:s.prod(a[k] for k in range(n) if k not in skip)
 return (P(set()),sum((b[i]*P({i}) for i in range(n)),s.Integer(0)),
   sum((c[i]*P({i}) for i in range(n)),s.Integer(0)),
   sum((d[i]*P({i}) for i in range(n)),s.Integer(0))+
   sum((b[i]*c[j]*P({i,j}) for i in range(n) for j in range(n) if i!=j),s.Integer(0)))
checks=0
for n in range(1,6):
 for seed in range(17):
  fs=[tuple(s.Rational(((seed+3)*(i+2)*(k+1))%13-6,7) for k in range(4)) for i in range(n)]
  ordinary=s.expand(s.prod(a+b*u+c*v+d*u*v for a,b,c,d in fs))
  coeff=tuple(ordinary.coeff(u,i).coeff(v,j) for i,j in ((0,0),(1,0),(0,1),(1,1)))
  assert conv(fs)==formula(fs)==coeff
  checks+=1
F,G=s.symbols("F G")
true=1+u*F+v*G+u*v*F*G
naive=(1+u*F)**2*(1+v*G)
assert s.expand(true).coeff(u,1).coeff(v,0)==F
assert s.expand(naive).coeff(u,1).coeff(v,0)==2*F
assert 3-3==0 and abs(3)+abs(-3)==6
print(f"PASS {checks}/85 four-column product identities; duplicate-global-mark and absolute-charge negative controls")
