#!/usr/bin/env python3
"""5D SU2 YM static BPST instanton-particle: exact energy/scale discriminator.

CLASSICAL: Belavin, Polyakov, Schwartz and Tyupkin (1975), instantons;
self-duality/Bogomolny 4D Euclidean Yang-Mills energy bound.
This is a radial density check of their explicit charge-one BPST solution,
NOT a new instanton construction or a proof of the 5D Einstein-YM system.
DASHI ORIGINAL OWNERS: BalabanSU2QuaternionCarrier; SU2Bracket369OrientationBridgeExact;
CompactLieLatticeGauge. No literal field-identification with the BPST gauge
connection has yet been constructed in those native discrete carriers.
USER: reuse the 369 YM programme for the KK/Hopf vortex/particle steelman.
THIS ROUND: exact mass integral and scale-degeneracy negative control.
"""
import sympy as s

r, rho, g5 = s.symbols("r rho g5", positive=True)
# Conventional SU(2) generators with Tr(T_a T_b)=1/2 delta_ab
# and F^a_ij F^a_ij = 192 rho^4 / (r^2+rho^2)^4.
F2 = 192*rho**4/(r*r+rho*rho)**4
volS3 = 2*s.pi**2
radial_integral = s.integrate(r**3*F2, (r,0,s.oo))
assert s.simplify(radial_integral-16) == 0
integratedF2 = s.simplify(volS3*radial_integral)
assert s.simplify(integratedF2-32*s.pi**2) == 0
mass = s.simplify(integratedF2/(4*g5**2))
assert s.simplify(mass - 8*s.pi**2/g5**2) == 0
# Core scale rho>0 is a genuine modulus of classical R4 YM action,
# unlike the illustrative Derrick-Skyrme E(R)=aR+b/R.
assert s.diff(mass,rho) == 0
# In R3xS1 with compact KK fibre, this particular R4 BPST formula
# is NOT automatically periodic or a caloron solution.
print("PASS BPST charge-one F_ij^a F_ij^a: integral R4 = 32*pi^2")
print("PASS static 4+1 SU2 Yang-Mills energy = 8*pi^2/g5^2")
print("PASS exact classical scale degeneracy: dE/d(rho) = 0")
print("OPEN original SU2 gauge potential/curvature explicit field weld")
print("OPEN R3xS1 caloron and coupled Einstein-YM backreaction")
print("OPEN collective-rotation/exchange configuration space and quantum spin")
