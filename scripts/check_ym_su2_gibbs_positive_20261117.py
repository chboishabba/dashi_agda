#!/usr/bin/env python3
"""Exact rational algebra for finite Bishop-quaternion Wilson deficit.

The corresponding Agda owner uses actual Bishop real square nonnegativity
and positive exp inverse; this script is ONLY a rational mathematical
reference. It does not validate original 4D Wilson source identification.
"""
from fractions import Fraction as F
from itertools import product
import sympy as sp

a,b,c,d=sp.symbols("a b c d", real=True)
norm=a*a+b*b+c*c+d*d
chord=(a-1)**2+b*b+c*c+d*d
assert sp.expand(F(1,2)*chord - (1-a) - F(1,2)*(norm-1))==0
tests=1

axis=[]
for i in range(4):
 for sign in (-1,1):
  q=[F(0)]*4;q[i]=F(sign);axis.append(q)
halves=[list(s) for s in product((F(-1,2),F(1,2)),repeat=4)]
nodes=axis+halves
assert len(nodes)==24
tests+=1
for q in nodes:
 qnorm=sum(v*v for v in q)
 sq=sum((q[0]-1 if i==0 else q[i])**2 for i in range(4))
 deficit=1-q[0]
 assert qnorm==1
 assert sq==2*deficit
 assert deficit>=0
 tests+=3
for beta in (F(0),F(1,7),F(3,2)):
 for q in nodes:
  assert beta*(1-q[0])>=0
  tests+=1
 print("beta",beta,"min action",min(beta*(1-q[0]) for q in nodes))
print(f"BISHOP_SU2_GIBBS_RATIONAL_DEFICIT_PASS={tests}")
