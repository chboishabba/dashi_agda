#!/usr/bin/env python3
"""Section38 exact arithmetic and timeline regression.

NS: exact radius condition Emax < 2 ν R² ε forces the
time-integrated upper envelope below ε.
PNP: two executions with the same retained initial state and
different terminal Boolean output must differ in an observation
at some clock step j<k; checks finite deterministic machines.
Hodge/BSD/RH cannot be promoted from these finite controls.

This is not a Lean/Agda kernel or Clay endpoint acceptance.
"""
from fractions import Fraction as Q
from itertools import product
from math import prod

checks={"NS_epsilon":0,"NS_negative_radius":0,"PNP_preterminal":0}
for nu,emax,eps in product(
        (Q(1,2),Q(1),Q(3,2)),
        (Q(0),Q(1),Q(9)),
        (Q(1,100),Q(1,4),Q(1))):
    # An explicit radius greater than the exact required threshold:
    # R² > Emax/(2*nu*eps).
    ratio=emax/(2*nu*eps)
    R=1+ratio
    assert R>0
    assert emax<2*nu*R*R*eps
    for E0 in (Q(0),emax/2,emax):
        budget=E0/(2*nu*R*R)
        assert budget<eps
        checks["NS_epsilon"]+=1
    # Intentionally too-small radii cannot be blindly certified.
    if emax>0:
        r=Q(1,100)
        if not (emax<2*nu*r*r*eps):
            assert emax/(2*nu*r*r)>=eps
            checks["NS_negative_radius"]+=1

# Exhaust deterministic 1-bit state machines with two possible
# observations, fixed initial states and a 2-step clock.
# A closed observer reads only the identical retained state.
# Distinct terminal values require at least one preterminal deviation.
for transitions in product(range(2),repeat=4):
    def step(s,o):
        return transitions[2*s+o]
    for obs_x in product(range(2),repeat=2):
        for obs_y in product(range(2),repeat=2):
            sx=sy=0
            history=[]
            for j in range(2):
                # Choose the readout as the current state:
                rx,ry=sx,sy
                history.append((obs_x[j]!=rx,obs_y[j]!=ry))
                sx=step(sx,obs_x[j])
                sy=step(sy,obs_y[j])
            if sx!=sy:
                assert any(a or b for a,b in history)
                checks["PNP_preterminal"]+=1
print("CLAY38 EXACT CHECKS PASS",checks,"TOTAL",sum(checks.values()))
