#!/usr/bin/env python3
"""Section39 exact algebraic nonpromotion controls for owner proofs.

NS one uniform positive radius is selected before varying E_N<=Emax.
YM true omitted B factorial coefficient and signed power are tested
over both signs and all low-degree corners, not only coefficient mass.
BSD two-crossing strict max geometric moment source for n>=1.
Hodge original Q0 quadratic derivative partner sign and branch.
PNP same-source deterministic 2-state terminal divergence requires a
paired observation difference before k, NOT a SAT time lower bound.

These are finite exact checks; cannot replace Lean/Agda acceptance.
"""
from fractions import Fraction as Q
from math import factorial
from itertools import product
import sympy as s

counts={"YM_signed_last_B":0,"NS_uniform_R":0,
        "BSD_strict_max_floor":0,"Hodge_signed_partner":0,
        "PNP_paired_preterminal":0}
quarter=Q(1,4)
for n in range(80):
    bn=Q(1,factorial(2*n+3))
    for X in (Q(-1,4),Q(-1,8),Q(0),Q(1,8),Q(1,4)):
        actual=2*X*bn*(X**n)
        assert abs(actual)==2*bn*abs(X)**(n+1)
        assert abs(actual)<=quarter**(n+1)
        counts["YM_signed_last_B"]+=2

for nu,Emax,epsilon in product(
        (Q(1,4),Q(1,2),Q(2)),
        (Q(0),Q(1,20),Q(1),Q(6)),
        (Q(1,100),Q(1,4),Q(2))):
    R=1+Emax/(2*nu*epsilon)
    assert R>0 and Emax<2*nu*R*R*epsilon
    for E0 in (Q(0),Emax/2,Emax):
        assert E0/(2*nu*R*R)<epsilon
        counts["NS_uniform_R"]+=1

for a,b in ((Q(1,2),Q(3,4)),(Q(2),Q(5)),
            (Q(5),Q(2)),(Q(4,3),Q(7,3))):
    h=[Q(1)]
    for n in range(1,42):
        h.append(a*h[-1]+b**n)
    r=a+b+1
    m=lambda j: Q(0) if j==0 else r**j
    for n in range(1,40):
        assert h[n]*m(n+2)-h[n+1]*m(n+1)>0
        assert m(n+2)>max(a,b)**n*m(2)
        counts["BSD_strict_max_floor"]+=2

d,c,u=s.symbols("d c u")
# Exactly the Q0 source first-jet type:
# Q0(s+h)-Q0(s)=h*(dField(s)-2h)
Q0=lambda z:-2*z*z+d*z+c
dField=lambda z:d-4*z
for sval in (s.Integer(0),s.Rational(1,3),u,s.Rational(-2,7)):
    partner=sval+dField(sval)/2
    assert s.expand(Q0(partner)-Q0(sval))==0
    assert s.expand(dField(partner)+dField(sval))==0
    assert s.expand(partner+dField(partner)/2-sval)==0
    counts["Hodge_signed_partner"]+=3

# Exhaust small deterministic two-source observation/time streams.
for transitions in product((0,1),repeat=4):
    step=lambda st,obs:transitions[2*st+obs]
    for ox in product((0,1),repeat=3):
        for oy in product((0,1),repeat=3):
            x=y=0
            seen=False
            for k in range(1,4):
                if ox[k-1]!=oy[k-1]:seen=True
                x=step(x,ox[k-1])
                y=step(y,oy[k-1])
                if x!=y:
                    assert seen
                    counts["PNP_paired_preterminal"]+=1

print("SECTION39 EXACT FINITE CONTROLS PASS",counts,
      "TOTAL",sum(counts.values()))
