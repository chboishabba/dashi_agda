#!/usr/bin/env python3
"""Selected first-Tits trinification: source E32/E33 + GS + EW photon rank.

ORIGINAL source #1106 E32,E33 VEV and six-invariant scalar potential;
#1241 orbifold P_L=P_R=diag(-,-,+) and 27 parity/anomaly tables.
Scientific source: von Gersdorff & Quiros PRD68 (2003) 105002,
DOI 10.1103/PhysRevD.68.105002 (localized anomalies and GS).
This is an EXACT FINITE Cartan mass matrix, not a complete 5D gauge,
anomaly/CS, scalar-minimum, or physical Weinberg-angle calculation.
"""
import sympy as s
P=(-1,-1,1)
UL=s.diag(-1,-1,2)
UR=s.diag(-1,-1,2)
H_L=s.diag(s.Rational(1,2),-s.Rational(1,2),0)
H_R=s.diag(1,-1,0)
# Neutral gauge basis (T3L, U1L, CENTRAL U1R, T3R).
def charge(l,r):
    return s.Matrix([H_L[l,l],UL[l,l],-UR[r,r],-H_R[r,r]])
phi=charge(2,1)      # Phi E32 from E6 owner
chi=charge(2,2)      # Chi E33 from E6 owner
ew=charge(1,0)       # even Chi E21 (Y=+1/2, T3L=-1/2)
gs=s.Matrix([0,1,-1,0])
assert tuple(phi)==(0,2,1,1)
assert tuple(chi)==(0,2,-2,0)
assert tuple(ew)==(-s.Rational(1,2),-1,1,-1)
assert gs==chi/2
assert P[1]*P[0]==1
Y=s.Matrix([0,s.Rational(1,6),s.Rational(1,6),-s.Rational(1,2)])
Q=s.Matrix([1,s.Rational(1,6),s.Rational(1,6),-s.Rational(1,2)])
assert all((v.T*Q)[0]==0 for v in (phi,chi,ew,gs))
assert all((v.T*Y)[0]==0 for v in (phi,chi,gs))
assert (ew.T*Y)[0]==s.Rational(1,2)
assert (ew.T*(Q-Y))[0]==-s.Rational(1,2)
def mass_gram(fields):
    return sum((q*q.T for q in fields),s.zeros(4))
m0=mass_gram([phi,chi])
mgs=mass_gram([phi,chi,gs])
mew=mass_gram([phi,chi,gs,ew])
assert (m0.rank(),mgs.rank(),mew.rank())==(2,2,3)
assert len(mew.nullspace())==1 and mew*Q==s.zeros(4,1)
print("PASS source E32/E33 gauge rank2, GS along anomalous U1 adds no new rank")
print("PASS orbifold-even Chi E21 EW doublet makes neutral rank3 of 4")
print("PASS unique photon Q=T3L+(UL+UR-3T3R)/6, untouched by GS direction")
print("OPEN source-derived EW potential/VEV: original E6 V6 Hessian does not provide E21 tachyon")
print("OPEN all non-Cartan gauge operators, gauge coupling constants, mixing angle, global anomaly/CS, full E6")
