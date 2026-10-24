#!/usr/bin/env python3
"""Restricted first-Tits SU3^3 orbifold parity-family UV no-go.

Keep colour P_c=I and SU2L on existing first two L coordinates,
so P_L=diag(-,-,+). Enumerate EVERY diagonal order-2 SU3R
element with det +1: I, (-,-,+),(-,+,-),(+,-,-).
One bulk Dirac 27 -> 4D left/right zero modes with gamma5*P.
Exact rational SU3c cubic and canonical U1L/R anomalies show
NO choice cancels both. Not a universal orbifold/no-new-matter
no-go, only the selected four-case family and its gauge consumer.
External group/orbifold prior art Slansky 1981,
Arkani-Hamed/Cohen/Georgi 2001, Scrucca et al 2002.
"""
from fractions import Fraction as F
from itertools import product
PL=(-1,-1,1)
UL=(-1,-1,2)
rightChoices=[(1,1,1),(-1,-1,1),(-1,1,-1),(1,-1,-1)]
for PR in rightChoices:
    UR=tuple(-1 if parity==-1 else 2 for parity in PR) \
        if PR!=(1,1,1) else (0,0,0)
    states=[]
    for c,l in product(range(3),range(3)):
        states.append((-PL[l],1,-UL[l],0))
    for c,r in product(range(3),range(3)):
        states.append((-PR[r],-1,0,UR[r]))
    for l,r in product(range(3),range(3)):
        states.append((-PL[l]*PR[r],0,UL[l],-UR[r]))
    assert len(states)==27
    colour=sum((F(hand*index,3) for hand,index,ql,qr in states),F(0))
    cubicL=sum(hand*ql**3 for hand,index,ql,qr in states)
    cubicR=sum(hand*qr**3 for hand,index,ql,qr in states)
    expected=(F(4),0,0) if PR==(1,1,1) else (F(0),40,-40)
    assert (colour,cubicL,cubicR)==expected
    assert colour!=0 or cubicL!=0 or cubicR!=0
    print("P_R",PR,"SU3c cubic",colour,"U1L cubic",cubicL,
          "U1R cubic",cubicR)
print("PASS no UV anomaly-free choice in this diagonal R-parity family for one Dirac27")
print("OPEN new boundary/spectator/GS matter or more general full-gauge orbifold")
