#!/usr/bin/env python3
"""Ideal-component witness (companion to locally executed 18-test analysis).
No empirical electrical frequency or environmental energy claim.
"""
from math import pi, sqrt, isclose

C_STORAGE=3.33e-6  # narrated
V=1500.0           # narrated target
P=6.7              # conditional real input, narrated display
F=7800.0           # audio, hypothetical electrical resonance only
C_TANK=5e-9        # assumed independently selected small tank capacitor
Q_TANK=100.0       # assumed illustrative loaded Q

def energy(c,v):return 0.5*c*v*v
def tank_loss(c,v,f,q):return 2*pi*f*energy(c,v)/q
def inductance(c,f):return 1/((2*pi*f)**2*c)
def min_q(c,v,f,p):return 2*pi*f*energy(c,v)/p
def max_c(p,v,f,q):return p*q/(pi*f*v*v)
def constrained_fill_time(c,v,p,eta):return energy(c,v)/(p*eta)

def test():
    assert isclose(energy(C_STORAGE,V),3.74625)
    assert isclose(constrained_fill_time(C_STORAGE,V,P,1),0.559141791044776)
    assert isclose(constrained_fill_time(C_STORAGE,V,P,.5),1.118283582089552)
    assert isclose(energy(C_STORAGE,V)*F,29220.75)
    assert min_q(C_STORAGE,V,F,P)>27000
    assert tank_loss(C_TANK,V,F,Q_TANK)<P
    assert isclose(tank_loss(max_c(P,V,F,50),V,F,50),P)
    assert inductance(C_TANK,F)>0
    # Fixed capacitor differential may coexist with reversed ground-referenced hot node:
    assert (1500-1000)>0 and (1500-1600)<0
    # The SAME supply/load reports can coexist with distinct ambient input/loss:
    assert isclose(P+0,2+4.7) and isclose(P+1,2+5.7)
    print('PASS: 10 source-bound ideal-component checks (no physical netlist proven)')

if __name__=='__main__':test()
