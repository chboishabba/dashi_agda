#!/usr/bin/env python3
"""Small-interval / odd KK controlled scale check for original #1106 V6.

This is a CONDITIONALLY NORMALIZED 5D scalar source, not a derived
Einstein/fermion/Green-Schwarz quantum vacuum. Physical original source
#1106 E32/E33, selected orbifold #1241. Known background is a ZERO-MODE
stationary source, not a literal constant 5D E-L solution.

With canonical source scalar kinetic scale v² and dimensionful bulk
potential scale v⁴, the dimensionless interval coordinate u=y/L
has E-L f_uu=(v L)^2 grad(V6), and its brane potential must carry
the SAME integrated coefficient (vL)^2 for the preceding effective
zero-mode stationarity to approximate the full 5D action.

At b0=1e-24 metres and L=pi*b0 the source's 10TeV trial vev
gives eps=vL~1.592e-4. The leading Robin-matched symmetric
nonconstant correction to t(u) is eps²*(dV6/dt)*(u-1/2)²/2.
This tiny correction explains why constant zero-mode truncation
may be EXCELLENT while it remains mathematically NOT an exact 5D
solution. Source-dependent coefficients/tunings are NOT established.

Odd scalar fluctuations with Dirichlet endpoints have the Poincare
gap (pi/L)^2 = 1/b0², so the old *constant-source* negative
orbifold-odd bulk Hessian eigenvalue ~-0.106585 does NOT by itself
make an actual 5D tachyon. Use crude conservative λ_min(Hodd)>-10
under this selected constant background, giving mass² positive.
Not a full interval-background all-field spectrum/stress certificate.
"""
from math import pi
from sympy import Rational
hbarc=0.1973269804e-15 # GeV m
b_m=1e-24
v_GeV=10000.0
b_GeV_inverse=b_m/hbarc
L=pi*b_GeV_inverse
epsilon=v_GeV*L
t=0.0246
source_t_force=t*(6-13*t*t)
assert source_t_force>.14
# After normalising two equal endpoint W's, W'=-V6'/2.
# From f''=eps² V6'(t) and equal endpoint Robin:
# f(u)=t+eps²*(V6'(t)/2)*(u-.5)^2 + O(eps^4),
# modulo one constant O(eps²) shifted by higher-order balance.
endpoint_minus_centre=epsilon**2*source_t_force/8
assert 4e-10<endpoint_minus_centre<5e-10
odd_hessian_lower=-10 # conservative source test threshold, NOT verified universal
KK_gap=1/b_GeV_inverse
odd_mass_sq_bound=KK_gap**2+odd_hessian_lower*v_GeV**2
assert odd_mass_sq_bound>0
assert epsilon<.0002
print("selected physical reference 1/b0 GeV",KK_gap)
print("eps=v*pi*b0",epsilon,"eps^2",epsilon**2)
print("selected old bulk force",source_t_force)
print("leading expected t boundary-centre profile difference",endpoint_minus_centre)
print("odd Dirichlet n=1 mass² lower bound GeV² if lambda_min>=-10",odd_mass_sq_bound)
print("PASS conditional small-interval scale separation; uniform zero-mode approximation can be good but is NOT a 5D E-L solution")
print("OPEN actual 5D coefficients, full 18-even+odd background spectral operators, boundary stress and quantum regulated radion")
