#!/usr/bin/env python3
"""Exact original L=1 periodic Wilson commutator coefficients.
At L=1 each positive plane uses [U_a,U_b], not four distinct links.
24-cell 5-design is exact for first two beta coefficients, as each
integrand has degree at most 4 in each of four link quaternions.
This is finite algebra, not an Agda/Haar construction.
"""
from itertools import product
from fractions import Fraction as Q
v=[]
for i in range(4):
 for s in (-1,1):
  q=[Q(0)]*4;q[i]=Q(s);v.append(tuple(q))
for signs in product((-1,1),repeat=4):
 v.append(tuple(Q(s,2) for s in signs))
assert len(v)==24
def mul(q,r):
 a,b,c,d=q;e,f,g,h=r
 return (a*e-b*f-c*g-d*h,a*f+b*e+c*h-d*g,
         a*g-b*h+c*e+d*f,a*h+b*g-c*f+d*e)
def inv(q):return(q[0],-q[1],-q[2],-q[3])
def t(q,r):return mul(mul(mul(q,r),inv(q)),inv(r))[0]
checks=0
first=second=Q(0)
for q in v:
 for r in v:
  x=t(q,r);first+=x;second+=x*x
  checks+=2
first/=24*24;second/=24*24
assert first==Q(1,4) and second==Q(1,3)
checks+=2
conditional=[]
for q in v:
 x=sum((t(q,r) for r in v),Q(0))/24
 assert x==q[0]*q[0]
 conditional.append(x)
 checks+=1
shared=sum(x*x for x in conditional)/24
disjoint=first*first
assert shared==Q(1,8) and disjoint==Q(1,16)
checks+=2
# Six pairs of four axes, 12 share one axis, 3 are disjoint.
T1=6*first
T2=6*second+2*(12*shared+3*disjoint)
S1=6-T1
S2=36-12*T1+T2
assert (T1,T2,S1,S2)==(Q(3,2),Q(43,8),Q(9,2),Q(187,8))
checks+=4
print(f"L1: Z(beta)=1-{S1} beta+{S2/2} beta^2+O(beta^3)")
print("EXACT_L1_SU2_COMMUTATOR_PASS",checks)
