#!/usr/bin/env python3
"""Exact inherited SM charge-table convention vs QED/QCD/Higgs.

DASHI owners: U1YChargeAssignmentTableReceipt,
AnomalyCancellationVerificationReceipt, HiggsElectroweakBoundary.
This checks inherited physical Standard Model data, not a derived
five-dimensional electroweak particle spectrum or observed Yukawas.
"""
from fractions import Fraction as F
Q_L=F(1,6); U_R=F(2,3); D_R=F(-1,3)
L_L=F(-1,2); E_R=F(-1); N_R=F(0); H=F(1,2)
fermions={
 'u_L':(F(1,2),Q_L,F(2,3)),
 'd_L':(F(-1,2),Q_L,F(-1,3)),
 'nu_L':(F(1,2),L_L,F(0)),
 'e_L':(F(-1,2),L_L,F(-1)),
 'u_R':(F(0),U_R,F(2,3)),
 'd_R':(F(0),D_R,F(-1,3)),
 'e_R':(F(0),E_R,F(-1)),
}
for name,(t3,y,charge) in fermions.items():
    assert t3+y==charge,name
assert F(1,2)+Q_L/2==F(7,12)!=F(2,3)
assert F(-1,2)+Q_L/2==F(-5,12)!=F(-1,3)
assert F(-1,2)+L_L/2==F(-3,4)!=-1
# All left-handed Weyl components; right-handed converted to conjugates.
left=[(6,Q_L),(3,-U_R),(3,-D_R),(2,L_L),(1,-E_R),(1,-N_R)]
assert sum(k*y**3 for k,y in left)==0
assert sum(k*y for k,y in left)==0
assert 3*Q_L+L_L==0
assert 2*Q_L-U_R-D_R==0
assert (3+1)%2==0 # Witten global SU2 doublet parity
assert -Q_L+H+D_R==0 # down Yukawa
assert -Q_L-H+U_R==0 # up conjugate-Higgs Yukawa
assert -L_L+H+E_R==0 # charged lepton Yukawa
assert F(-1,2)+H==0 # photon survives neutral Higgs vev
print("PASS exact Q=T3+Y on seven SM fermion species/chiral states")
print("PASS previous Higgs Q=T3+Y/2 without doubling Y gives wrong 7/12 up charge")
print("PASS standard inherited cubic/mixed/gravitational anomalies and Witten SU2 parity")
print("PASS Yukawa and neutral Higgs generator hypercharges")
print("OPEN continuous 5D chiral spectrum, physical g/g' mixing and renormalised QED/QCD")
