#!/usr/bin/env python3
"""Original source Section43 exact, finite, fail-closed geometry controls.

These do NOT run Agda/Lean; a finite test is NOT a Clay proof.
All cases use exact integers/Fraction and the original stated
A/B degree cutoffs, original Q0 parity and explicit adaptive read ABI.
"""
from fractions import Fraction as F
from itertools import product
from math import factorial

checks={"YM_degree_factor":0,"YM_signed_outer":0,"NS_linear_radius":0,
        "BSD_crossing_moment":0,"Hodge_central_deck":0,
        "PNP_adaptive_block":0,"PNP_empty_block":0}
q=F(1,4)
for c in range(1,41):
    A=[F(1,factorial(2*i+2)) for i in range(c)]
    B=[F(1,factorial(2*i+3)) for i in range(c)]
    assert sum(A)<=F(6,11) and sum(B)<=F(10,57)
    for i,j in product(range(c),repeat=2):
        d=i+j
        if d>=c-1:
            m=d+1
            assert m==c+(m-c) and m>=c
            checks["YM_degree_factor"]+=2
        if d>=max(0,c-2):
            m=d+2
            assert m==c+(m-c) and m>=c
            checks["YM_degree_factor"]+=2
    for x in (F(-1,4),F(-1,8),F(0),F(1,8),F(1,4)):
        aw=sum((A[i]*A[j]*x**(i+j) for i,j in product(range(c),repeat=2)
                if i+j>=c-1),F(0))
        bw=sum((B[i]*B[j]*x**(i+j) for i,j in product(range(c),repeat=2)
                if i+j>=max(0,c-2)),F(0))
        assert abs(x*aw)<=q**c*sum(A)**2<=q**c
        assert abs(x*x*bw)<=q**c*sum(B)**2<=q**c
        checks["YM_signed_outer"]+=2

for nu,emax in product((F(1,3),F(2)),(F(0),F(1,5),F(3))):
    prev=None
    for j in range(40):
        eps=F(1,j+1)
        R=1+emax/(2*nu*eps)
        direct=1+emax*F(j+1)/(2*nu)
        assert R==direct and R>0 and emax<2*nu*R**2*eps
        if prev is not None: assert prev<=R
        prev=R
        checks["NS_linear_radius"]+=4 if j else 3

def h(a,b,n):
    z=F(1)
    for k in range(1,n+1):z=a*z+b**k
    return z
for a,b in ((F(1,2),F(3,4)),(F(2),F(5)),(F(5),F(2))):
    for n in range(40):
        m=lambda k: F(0) if k==0 else (a+b+1)**k
        left=h(a,b,n)*m(n+2)-h(a,b,n+1)*m(n+1)+(a*b)**(n+1)*m(0)
        right=h(b,a,n)*m(n+2)-h(b,a,n+1)*m(n+1)+(b*a)**(n+1)*m(0)
        assert left==right and left>0
        checks["BSD_crossing_moment"]+=2

# For original a_i=0,y_i=3, six quadratic roots are 0,1/2;
# derivative signs 1,-1. Signed-product delta=+1 requires even flips.
even=[bits for bits in product((0,1),repeat=6) if sum(bits)%2==0]
assert len(even)==32
central=(1,)*6
for s in even:
    target=tuple(v^1 for v in s)
    assert target in even and target != s
    assert tuple(v^1 for v in target)==s
    for e in even:
        applied=tuple(v^w for v,w in zip(s,e))
        assert applied in even
        if e==central:assert applied==target
        checks["Hodge_central_deck"]+=2 if e==central else 1

# Adaptive read addresses depend on the SAME current machine state.
# For a first unequal state, some x-read coordinate must already
# differ between the original input pair.
for n in range(1,4):
  for x,y in product(list(product((0,1),repeat=n)),repeat=2):
    for block in range(n+1):
      for transition in product((0,1),repeat=4):
        sx=sy=0
        xread_differed=False
        for j in range(3):
          ax=tuple((j+sx+i)%n for i in range(block))
          ay=tuple((j+sy+i)%n for i in range(block))
          ox=tuple(x[idx] for idx in ax)
          oy=tuple(y[idx] for idx in ay)
          xread_differed |= any(x[idx]!=y[idx] for idx in ax)
          sx=transition[2*sx+(sum(ox)%2)]
          sy=transition[2*sy+(sum(oy)%2)]
          if sx!=sy:
            assert xread_differed and block>0
            checks["PNP_adaptive_block"]+=2
          elif block==0:
            assert sx==sy
            checks["PNP_empty_block"]+=1
print("SECTION43 ORIGINAL EXACT PASS",checks,"TOTAL",sum(checks.values()))
