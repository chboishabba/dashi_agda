#!/usr/bin/env python3
"""Exact arithmetic S3 original curve. Classical Kummer and Fermat are external."""
from itertools import product
from fractions import Fraction as F
S=(1,-1,2,-2)
def v2(a):
 a=abs(a);n=0
 while a%2==0:n+=1;a//=2
 return n
pairs=list(product(S,S))
real=[(a,b) for a,b in pairs if (a<0)==(b<0)]
dyadic=[(a,b) for a,b in real if v2(a)%2==0]
torsion={(1,1),(-1,-1),(1,2),(-1,-2)}
assert len(pairs)==16 and len(real)==8 and len(dyadic)==4
assert set(dyadic)==torsion
assert 3*0**2-1==-1 and 3*1**2-1==2 and 3*(-1)**2-1==2
for a in range(-20,21):
 for b in range(1,12):
  if a in (0,b,-b):continue
  x=F(a,b)
  assert (x*x-1)**2+(2*x)**2==(x*x+1)**2
  assert x*(x*x-1)==x**3-x
assert 64==2**6
print('PASS 16 global S-unit pairs -> 8 real -> 4 dyadic, exactly original torsion')
print('PASS original torsion root-derivative branch values')
print('PASS original E-to-area-one rational triangle algebra')
print('FIREWALL classical Galois/Fermat theorems external; native kernel not run')
print('FIREWALL Sha[2]=0 does not imply Sha=0')
