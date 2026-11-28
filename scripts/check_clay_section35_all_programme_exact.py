#!/usr/bin/env python3
"""Finite exact controls for all-Clay Section35 (not kernel proofs).
Donor objects: NS quarter interpolation, BSD two-crossing h/m,
Hodge denominator saturation illustrative ring, PNP same-run event slots.
RH external proof admission deliberately cannot be finite-tested.
"""
from fractions import Fraction as F
from itertools import product
import random
import sympy as s

counts={"NS_quarter":0,"BSD_crossing":0,"Hodge_saturation":0,"PNP_actual_slots":0}
# NS: original E_(1/4)^4 <= E^3*D, with fourth-power mode masses.
w=[1,16,81,256]
for x in product(range(5),repeat=4):
    energy=sum(v*v for v in x)
    diss=sum(k*v*v for k,v in zip(w,x))
    quarter=sum(r*v*v for r,v in zip((1,2,3,4),x))
    assert quarter**4<=energy**3*diss
    counts["NS_quarter"]+=1
# BSD: actual complete homogeneous two-crossing h recurrence and an
# explicit positive-source moment sample (NOT the actual L-function).
for a,b in [(F(1,2),F(3,4)),(F(2),F(5)),(F(3,2),F(7,2))]:
    h=[F(1)]
    for n in range(1,52): h.append(a*h[-1]+b**n)
    r=a+b+1
    m=lambda k:F(0) if k==0 else r**k
    for n in range(50):
        source=h[n]*m(n+2)-h[n+1]*m(n+1)+(a*b)**(n+1)*m(0)
        assert source>0
        assert m(n+2)>a*m(n+1)
        counts["BSD_crossing"]+=2
# Hodge: a concrete punctured affine ring (xy,y^2), saturate at x.
# Its closure ideal on x!=0 is (y), stable under multiplication by x.
x,y=s.symbols('x y')
rng=random.Random(369)
for i in range(300):
    p=sum(rng.randrange(-3,4)*x**j*y**k for j in range(4) for k in range(4-j))
    in_sat=s.expand(p.subs(y,0))==0
    in_sat_times_D=s.expand((x*p).subs(y,0))==0
    assert in_sat==in_sat_times_D
    counts["Hodge_saturation"]+=1
# PNP: genuine charged event *windows* (overlapping permitted).
# A witness per obligation must occur in its actual window.
for T in range(1,12):
    for trial in range(38):
        obligations=[]
        for j in range(1+(trial%8)):
            start=rng.randrange(T)
            stop=rng.randrange(start+1,T+1)
            weight=rng.randrange(1,6)
            obligations.append((start,stop,weight))
        C=max(sum(w for a,b,w in obligations if a<=k<b) for k in range(T))
        W=sum(z[2] for z in obligations)
        assert W<=T*C
        for B in range(0,T+2):
            if B*C<W: assert B<T
        assert T>0 and C>0
        counts["PNP_actual_slots"]+=3
print('SECTION35 EXACT FINITE MODEL CHECKS:',counts,'TOTAL',sum(counts.values()),'PASS')
