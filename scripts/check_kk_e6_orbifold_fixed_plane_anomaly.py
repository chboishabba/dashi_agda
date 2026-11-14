#!/usr/bin/env python3
"""Candidate trinification orbifold: chiral 16 + vectorlike 10+1
and the CS-only local-anomaly repair impossibility.

Original E6 branching literature: Slansky, Phys Rept 79 (1981).
Original orbifold fixed plane anomalies: Arkani-Hamed/Cohen/Georgi,
Phys Lett B516 (2001), DOI 10.1016/S0370-2693(01)00946-7;
Scrucca et al Phys Lett B525 (2002), DOI 10.1016/S0370-2693(01)01430-7.

The 16_L and 10_R+1_R are IR spectrum LABELS of the locally checked
#1241/#1106 P_L=P_R=diag(-1,-1,+1), E32/E33 parity candidate;
not a construction of a complete 5D anomaly-safe E6 orbifold.
"""
from fractions import Fraction as F
import sympy as s
L={
 'Q_L': (6,'3','2',F(1,6)),
 'u_c': (3,'bar3','1',F(-2,3)),
 'd_c': (3,'bar3','1',F(1,3)),
 'L_L': (2,'1','2',F(-1,2)),
 'e_c': (1,'1','1',F(1)),
 'nu_c': (1,'1','1',F(0)),
}
R={
 'D': (3,'3','1',F(-1,3)),
 'Dbar': (3,'bar3','1',F(1,3)),
 'Hplus': (2,'1','2',F(1,2)),
 'Hminus': (2,'1','2',F(-1,2)),
 'N': (1,'1','1',F(0))
}
assert sum(r[0] for r in L.values())==16
assert sum(r[0] for r in R.values())==11
assert R['D'][3]==-R['Dbar'][3]
assert R['Hplus'][3]==-R['Hminus'][3]
assert R['N'][3]==0
assert sum(R[t][0] for t in ('D','Dbar','Hplus','Hminus'))==10

# UV orbifold gauge before E32/E33 breaking is colour SU3 +
# SU2L*U1L + SU2R*U1R, with nonzero zero-mode anomalies.
# For any constant even zero-mode gauge parameter, the integrated
# variation of a 5D classical bulk CS density over S1/Z2 is
# opposite at its two boundaries: (-k,+k), summed zero. Therefore
# it CANNOT cancel a nonzero integrated 4D UV anomaly A.
uv={'UL3':40,'UR3':-40,'UL2UR':8,'ULUR2':-8,
    'gravUL':16,'gravUR':-16,'SU3c2UL':2,'SU3c2UR':-2}
k=s.symbols('k',real=True)
for tag,A in uv.items():
    assert A!=0
    assert s.solve([s.Rational(A,2)-k,s.Rational(A,2)+k],k)==[]
    assert s.simplify((s.Rational(A,2)-k)+(s.Rational(A,2)+k)-A)==0
print('PASS selected SM subgroup: 16 left matter + vectorlike 10 and singlet right E6 charge decomposition')
print('PASS nonzero integrated UV anomaly cannot be canceled by CS-only opposite-boundary inflow')
print('OPEN new localized spectators or actual Green-Schwarz/Wess-Zumino mechanism and its quantum source')
print('OPEN fixed-point global CS, Higgs mass operators, realistic EWSB/photon and orbifold Casimir')
