#!/usr/bin/env python3
"""Exact CMP102 original factorial mass and signed residual checks.

Finite regression, not Agda kernel acceptance. The all-index source proof
uses factorial successor products and the rational fixed-point identity.
"""
from fractions import Fraction as F
from math import factorial

A0,B0=F(1,2),F(1,6)
QA,QB=F(1,12),F(1,20)
BA,BB=F(12,11),F(20,19)
assert 1+BA*QA==BA and 1+BB*QB==BB
assert BA*A0==F(6,11) and BB*B0==F(10,57)
C=F(6,11)**2+2*F(10,57)+F(10,57)**2
assert C == F(267004,393129) and C < F(3,4)
count={"ratio":0,"bank":0,"wing":0,"disk":0}
for n in range(0,500):
 a=F(1,factorial(2*n+2));b=F(1,factorial(2*n+3))
 an=F(1,factorial(2*n+4));bn=F(1,factorial(2*n+5))
 assert an <= QA*a and bn <= QB*b
 assert an/a == F(1,(2*n+4)*(2*n+3))
 assert bn/b == F(1,(2*n+5)*(2*n+4))
 count['ratio']+=4
sa=sb=F(0)
for n in range(0,190):
 a=F(1,factorial(2*n+2));b=F(1,factorial(2*n+3))
 assert sa+BA*a<=F(6,11) and sb+BB*b<=F(10,57)
 assert sa <= F(6,11) and sb<=F(10,57)
 sa+=a;sb+=b
 count['bank']+=4
for c in range(1,91):
 a=[F(1,factorial(2*j+2)) for j in range(c)]
 b=[F(1,factorial(2*j+3)) for j in range(c)]
 def conv(v):
  out=[F(0)]*(2*c-1)
  for i,vi in enumerate(v):
   for j,vj in enumerate(v):out[i+j]+=vi*vj
  return out
 aa=conv(a);bb=conv(b)
 for x in (F(-1,4),F(-1,7),F(0),F(1,7),F(1,4)):
  A=sum((v*x**j for j,v in enumerate(a)),F())
  B=sum((v*x**j for j,v in enumerate(b)),F())
  G=1-2*A-x*A*A+2*x*B+x*x*B*B
  Ta=sum((aa[j]*x**j for j in range(c-1)),F())
  Tb=sum((bb[j]*x**j for j in range(max(0,c-2))),F())
  tail=-x*(A*A-Ta)+2*x*b[-1]*x**(c-1)+x*x*(B*B-Tb)
  assert G==tail
  assert abs(G)<=C*abs(x)**c
  assert abs(G)<=F(3,4)*F(1,4)**c
  count['wing']+=2;count['disk']+=1
print('SECTION34 ORIGINAL CMP102 EXACT PASS:',count,'TOTAL',sum(count.values()),'CONSTANT',C)
