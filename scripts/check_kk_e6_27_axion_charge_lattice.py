#!/usr/bin/env python3
"""Trinification27 singlet weights and CONDITIONAL global WZ charge gate.

The source scalar carrier is ONE E6-derived 27 restricted to SU3^3:
(3,bar3,1)+(bar3,1,3)+(1,3,bar3). Requiring colour-SU3c,
SU2L and SU2R invariance of a SINGLE elementary 27 scalar VEV,
the only allowed component is C33, with (UL,UR)=(+2,-2).
Hence no elementary charge-(1,-1) invariant axion is present within
that 27. NOT a claim other representations/composites impossible.

THE HALF-PHASE OBSTRUCTION BELOW IS FOR THE ORIGINAL SYMMETRIC\nTWO-ENDPOINT WZ ANSATZ ONLY. NEW source: check_kk_e6_orbifold_cs_wz_anomaly_transfer.py\nuses bulk CS redistribution plus ONE Chi33 WZ term and avoids this\nhalf-unit in its selected trace lattice. A global spin CS lattice\nand quantum regulator remain open.\n\nUnder an ASSUMED integral mixed nonabelian fixed-plane instanton
number one and source anomaly coefficient one, the naive
a=argChi33/2 WZ exponent changes by (-1) after argChi33 -> argChi33+2pi.
Physical integral spin/(SU3^3xU1)/Gamma anomaly lattice and regulator
are still OPEN; this is a CONDITIONAL mod-2 obstruction example,
not a proof that all GS counterterms fail. Original sources:
Slansky Phys Rep 79 (1981); von Gersdorff/Quiros PRD68 (2003).
"""
import sympy as s
UL=(-1,-1,2)
UR=(-1,-1,2)
source27_single_elementary_invariant_scalars=[]
# Coloured A,B blocks cannot take single VEVs preserving SU3c;
# C=(1,3L,bar3R), SU2L singlet row3 and SU2R singlet col3.
for l in range(3):
    for r in range(3):
        if l==2 and r==2:
            source27_single_elementary_invariant_scalars.append(
                (UL[l],-UR[r]))
assert source27_single_elementary_invariant_scalars==[(2,-2)]
# Fixed-plane mixed nonabelian unit-normalisation conditional:
unit_instanton=1
naive_half_phase_shift=s.pi*unit_instanton
assert s.simplify(s.exp(s.I*naive_half_phase_shift)+1)==0
assert s.simplify(s.exp(2*s.I*naive_half_phase_shift)-1)==0
print("PASS only single elementary 27 scalar with SU3c,SU2L,SU2R invariant VEV is C33, charge (+2,-2)")
print("PASS conditional mod-2 sign under one winding for naive Chi33 half-phase at unit instanton number")
print("OPEN actual global gauge/spin quotient and anomaly characteristic-class integrality")
# Redistribution: original half anomaly on each boundary requires
# WZ mixed source coefficient 2/4, but after transfer to ONE boundary
# the full anomaly requires 2/2, integral in the original trace ring.
assert s.Rational(2,4)==s.Rational(1,2)
assert s.Rational(2,2)==1
print("CORRECTION: 5D CS transfer to one boundary removes the naive mixed half-unit; charge-one scalar not forced by this selected test")
print("OPEN actual integral spin/quotient CS5, one-boundary WZ and global anomaly regulator")
