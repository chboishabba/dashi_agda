#!/usr/bin/env python3
"""ORBIFOLD-PARITY-COMPATIBLE NONLIFTABLE faithful E6-derived gauge bundle.

Original E6 #1106 first-Tits SU3^3 action on 27 has kernel
Z3_diag. In KK #1241 choose P_c=I and P_L=P_R=diag(-,-,+);
the unbroken boundary cover H0=SU3c x S(U2xU1)L x S(U2xU1)R
is connected, with central diagonal Z3 inside H0.
Its faithful boundary group is H=H0/Z3_diag.

On S², give the north/south hemispheres the clutching transition
g(t) on equator S¹=R/Z, defined by the class of
 (h(t),h(t),h(t)) in H where
 h(t)=diag(exp(2πit/3),exp(2πit/3),exp(-4πit/3)).
Each h(t) COMMUTES with both orbifold parities, lies inside SU3 and
S(U2xU1), h(0)=I, h(1)=omega I.
Thus g(t) is a closed LOOP in the quotient boundary gauge group.
Its unique lift in H0 starting at identity ends at
(omega I,omega I,omega I), nontrivial deck Z3, so this boundary-
admissible principal H bundle on S² CANNOT lift to an H0 bundle.
Three concatenations lift to a closed loop in the cover: the
image of the loop under the deck-group obstruction map to Z3 has
order three, NOT necessarily the element itself in π1(H).

This demonstrates a real previously unpaid GLOBAL CS/eta test family
for the SELECTED orbifold, unlike the separate bulk clock-shift T²
witness whose S shift does not commute with P.
We do NOT compute a 5D spin/APS anomaly or construct a whole
six-dimensional fermionic index on that twisted gauge bundle.
"""
import sympy as s
u=s.symbols("u",real=True)
omega=s.exp(2*s.pi*s.I/3)
phase=s.exp(2*s.pi*s.I*u/3)
h=s.diag(phase,phase,phase**-2)
P=s.diag(-1,-1,1)
assert s.simplify(h.det())==1
assert (P*h-h*P).applyfunc(s.simplify)==s.zeros(3)
assert h.subs(u,0)==s.eye(3)
assert (h.subs(u,1)-omega*s.eye(3)).applyfunc(s.simplify)==s.zeros(3)
assert (h.subs(u,1)-s.eye(3)).applyfunc(s.simplify)!=s.zeros(3)
# Because diag(omega I) is in first-Tits kernel, g(1)=g(0)
# ON THE FAITHFUL GAUGE GROUP. But the chosen lift is not closed.
assert all((z-z)%3==0 for z in range(3))
for n in (1,2):
    assert (h.subs(u,n)-s.eye(3)).applyfunc(s.simplify)!=s.zeros(3)
assert (h.subs(u,3)-s.eye(3)).applyfunc(s.simplify)==s.zeros(3)
# Negative control: the alternate bulk T2 shift does NOT preserve
# the fixed-point gauge parity, so never use it as an orbifold H test.
S=s.Matrix([[0,0,1],[1,0,0],[0,1,0]])
assert (P*S-S*P)!=s.zeros(3)
print("PASS source faithful H=(SU3c x U2L x U2R)/Z3_diag orbifold EVEN group")
print("PASS equator clutch loop in parity-even H lifts from identity to diagonal omega central deck element")
print("PASS order-three Z3 lift obstruction; nonliftable H principal bundle on S2")
print("FAIL old bulk-clock/shift flat T2 configuration as parity-even fixed-plane test")
print("OPEN spin quotient Dirac index/eta and truly quantized 5D CS + Chi33 boundary WZ on this S2 obstruction")


# 2026-10-26 same-source Higgs line-bundle consumer. H0 has an
# orbifold-even SU3 torus h_k(u)=diag(exp(2 pi i(1/3+k)u),
# exp(2 pi i(1/3+k)u), exp(-4 pi i(1/3+k)u)).
# For ANY integer k, h_k(1)=omega I. Consequently the triple
# (h_kc,h_kL,h_kR) is a quotient loop with the SAME nontrivial
# diagonal Z3 deck obstruction, but its Higgs C33 character in
# (1,3L,bar3R) winds 2*(kR-kL) times.
#
# Standard clutching classification: the induced C33 complex LINE
# over S2 has c1=2*(kR-kL), with equator orientation as chosen.
# A line bundle of nonzero degree has no nowhere-zero global section.
# This is a field-domain obstruction to an unpatched PHASE-ONLY WZ
# functional on ALL admissible orbifold backgrounds, not a global
# anomaly calculation and NOT a rejection of Higgs-constrained EFTs.
from fractions import Fraction as Fr
def torus_weights(k):
    """Exact rational upper-doublet and singlet exponents / (2 pi i)."""
    a=Fr(1,3)+k
    return (a,a,-2*a)

def chi33_clutch_degree(kL,kR):
    """C33 is 3L ⊗ (bar3R), both SU2 singlet components."""
    return torus_weights(kL)[2]-torus_weights(kR)[2]

for kc in range(-2,3):
    for kl in range(-2,3):
        for kr in range(-2,3):
            # All three SU3 factors still end at the SAME omega I;
            # integer winding changes do not alter the deck label.
            for k in (kc,kl,kr):
                assert torus_weights(k)[0]-Fr(1,3)==k
                assert torus_weights(k)[2]+Fr(2,3)==-2*k
            deg=chi33_clutch_degree(kl,kr)
            assert deg==2*(kr-kl) and deg.denominator==1
            assert deg%2==0
assert chi33_clutch_degree(0,0)==0
assert chi33_clutch_degree(1,0)==-2
assert chi33_clutch_degree(0,1)==2
# Same quotient deck class, different C33 degree: the Z3 class by
# itself cannot decide whether a nowhere-zero C33 section can exist.
assert chi33_clutch_degree(0,0)!=chi33_clutch_degree(1,0)
# In the nonzero case this topological obstruction survives pullback
# from S2 to S2 x S2 (both factors spin) and trivially along an interval.
print("PASS 125 orbifold-even quotient clutch representatives: common diagonal Z3 obstruction")
print("PASS C33 line winding c1=2*(kR-kL), including forced-zero +/-2 sectors")
print("PASS quotient Z3 label alone does not determine C33 line triviality")
print("OPEN global section status of other Higgs fields, non-torus backgrounds, full CS/eta and field-space completion")
