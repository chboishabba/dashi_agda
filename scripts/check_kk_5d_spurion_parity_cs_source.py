#!/usr/bin/env python3
"""5D paired QCD source: gauge-invariant spurion masses + parity/CS audit.

This is a CANDIDATE interacting local EFT, not a supersymmetric or UV-complete
5D action. A neutral real scalar X has potential lambda(X^2-w^2)^2.
Dirac masses M_i+y_i <X>; charged scalar masses^2 mu_i^2+kappa_i<X>^2.
Gauge interactions and Yukawa/scalar-spurion couplings are nonzero.
The X fluctuation contributes an EXTRA physical determinant, not included
in the earlier free-paired eight-flavour Casimir plot.

The eight SU3 fundamental vectorlike 5D Dirac charge assignments are
q=(+2,-1) in minimum QED e/3 units, 4 of each. The one-loop induced
5D CS shifts depend on regulator conventions and mass signs: only
necessary integrality checks are performed here. Source for 5D
parity-CS shift: 2024 CMP "Comments on Global Symmetries and
Anomalies of 5d SCFTs" doi:10.1007/s00220-024-05139-8.
Global quotient-group CS/bordism classification is OPEN.
"""
from fractions import Fraction as F
from math import pi
quark_5d_GeV=[.00216,.00470,.0935,1.273,4.183,172.56,9000.,9000.]
charge_minimal=[2,-1,-1,2,-1,2,2,-1]
assert len(quark_5d_GeV)==len(charge_minimal)==8
assert charge_minimal.count(2)==charge_minimal.count(-1)==4

# An INTERACTING (but nonrenormalizable) 5D Yang-Mills/Dirac/bifundamental/
# spurion EFT can produce the requested masses:
# L_m=-sum (M_i+y_i X) psibar_i psi_i
# L_s=-sum (mu_i^2+kappa_i X^2)|S_i|^2
# V_X=lambda_X(X^2-w^2)^2; X is gauge neutral and w=1000 GeV.
# Distinct S_i live in fundamental and conjugate pairs and have actual
# nonzero gauge-covariant kinetic terms.
w=1000.
lamX=.4
fermion_y=[0.]*6+[1.,1.]
fermion_M=quark_5d_GeV[:6]+[8000.,8000.]
scalar_k=[1.]*8
scalar_mu_sq=[3000.**2-w*w]*8
dirac_mass=[m+y*w for m,y in zip(fermion_M,fermion_y)]
scalar_mass_squared=[mu+k*w*w for mu,k in zip(scalar_mu_sq,scalar_k)]
assert dirac_mass==quark_5d_GeV
assert all(abs(m-3000.**2)<1e-8 for m in scalar_mass_squared)
# Physical spurion radial excitation at X=w:
mX2=8*lamX*w*w # canonical potential lambda_X (X^2-w^2)^2
assert mX2>0 and abs(mX2-3200000.)<1e-9
mX=mX2**.5
assert abs(mX-1788.8543819998317)<1e-8
print("PASS candidate gauge-invariant local X-dependent masses, mX GeV",mX)
print("EXTRA missing one-loop determinant: 1 real neutral spurion mode at mX")

# Basic charge-lattice descent of (SU3 x U1)/Z3:
# (centre omega, U1 omega) acts as omega^(triality+charge_min).
for q in charge_minimal:
    assert (1+q)%3==0
assert (-3)%3==0  # singlet electron q=-3
assert (+3)%3==0  # optional heavy charged singlet q=+3
print("PASS proposed SU3xU1 charges descend through diagonal Z3")

# 5D parity-odd determinant: under common POSITIVE fermion mass
# sign, fundamental SU3 shifts by half its cubic index per field.
# Fractional parts are convention-independent, but integral CS
# LEVELS STILL REQUIRE A SPECIFIC BARE COUNTERTERM/REGULATOR.
sign=[1]*8
cubic_SU3=F(sum(sign),2)       # 8 fundamentals at A_fund=1
mixed_SU3sqU1=F(sum(q*s for q,s in zip(charge_minimal,sign)),2)
U1_cub=F(3*sum(q**3 for q in charge_minimal),2)
U1_grav=F(3*sum(charge_minimal),2)
# two physical SU3-singlet Dirac spinors, electron q=-3 and
# optional heavy unit-electromagnetic-charge q=+3 cancel
# bare cubic/gravitational shifts if their mass signs agree.
U1_cub+=F((-3)**3+3**3,2)
U1_grav+=F(-3+3,2)
assert (cubic_SU3,mixed_SU3sqU1,U1_cub,U1_grav)==(4,2,42,6)
assert all(x.denominator==1 for x in
           (cubic_SU3,mixed_SU3sqU1,U1_cub,U1_grav))
# CRITICAL: integer local coefficients do not establish the
# (SU3xU1)/Z3 global CS action/large gauge transformation phases.
# Massive 5D Dirac scalar bilinears also generally select a
# parity-breaking sign; even Nf alone does not make P invariant.
print("SU3 induced half cubic coefficient:",cubic_SU3)
print("SU3sqU1 conditional mixed half-sum:",mixed_SU3sqU1)
print("U1^3 conditional integer charge half-sum:",U1_cub)
print("U1-grav conditional half-sum:",U1_grav)
print("PASS necessary local parity-CS arithmetic; global quotient, bare levels, regulator, full E6 fermions OPEN")
print("FAIL exact 5D orientation reflection parity for unequal positive fermion masses without parity-exchanged negative-mass partners")
print("FAIL previous free-one-loop same-action completeness: neutral propagating spurion determinant omitted; recompute all vacuum derivatives")
