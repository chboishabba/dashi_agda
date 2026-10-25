#!/usr/bin/env python3
"""Source-gated one-stage flat/curved selected-W horn rejection.

Provenance: Hatcher AT Ex 2B.2 supplies the linked child commutator;
original selected W rational norm-squared lower is neutrino Agda #1247
and its independent hyperfabric #1249 certificate. The sharp spectral
arc commutator inequality is newly derived in current #1249, not
attributed to Gotô's 1949 abstract commutator-surjectivity theorem.

Source acceptance: if one GENUINE child meridian has d(B)<=3/5,
and the BASED parent-to-actual-commutator Wilson defect eta<=3/1000,
then the selected root is impossible. For flat eta=0, this is simpler.
NO actual Hatcher meridian length, Stokes surface or physical eta is supplied.
"""
from fractions import Fraction as F
root_sq=F(854996726408,648677790003)
child_sq_cap=F(819,625)   # sharp direct commutator when d(B)<=3/5
root_rational_low=F(287,250)
child_rational_high=F(229,200)
eta_cap=F(3,1000)
assert root_sq>root_rational_low**2
assert child_sq_cap<child_rational_high**2
assert child_rational_high+eta_cap==root_rational_low
print('PASS exact one-stage CURVED source rejection: d(child)<=3/5, eta<=3/1000')
assert root_sq>child_sq_cap
print('PASS FLAT limit eta=0, exact root-child contradiction')

# One REAL based homotopy/curvature area budget must bound eta;
# synthetic M=4, L=3/20 -> M L=3/5, Fmax=3/100,
# area<=1/10 implies K*A=3/1000. This is deliberately NOT
# a spatial certificate for the source wild horn.
M,L,K,area=F(4),F(3,20),F(3,100),F(1,10)
assert M*L==F(3,5)
assert K*area==eta_cap
print('PASS synthetic same-connection metric-plus-curvature acceptance numbers')

# Fail-closed: eta=1/100 >3/1000 gives no certified rejection.
assert F(1,100)>eta_cap
# Without actual Hatcher class/loop and based homotopy, a matching
# isolated SU3 interferometer W is not evidence of a horn topology.
print('PASS fail-closed larger curvature defect and absent same-object marking')
