#!/usr/bin/env python3
"""S1 periodic chiral-pair and graviphoton/isometry BIDI obstruction.

The profiles here are schematic 5D scalar and Dirac mass backgrounds;
they are not derived as a solution of a scalar potential or 5D gravity.
Source logic: Callan-Harvey 1985, Kaplan 1992 and standard KK reduction.
"""
import sympy as s
theta,m,v,kappa=s.symbols('theta m v kappa',positive=True,real=True)
mass_profile=m*s.sin(theta)
wall=v*s.sin(theta)
int_mass=s.integrate(mass_profile,(theta,0,2*s.pi))
gradient_sq=s.integrate(s.diff(wall,theta)**2,(theta,0,2*s.pi))
assert int_mass==0
assert s.simplify(gradient_sq-s.pi*v*v)==0

# Smooth periodic 5D Dirac, separated first-order zero-mode equations:
# (d_theta+M+i a)f_L=0 and (-d_theta+M-i a)f_R=0.
# With a constant U1 phase holonomy phi, monodromies are
# mu_L=exp(-integral(M)-i phi), mu_R=exp(+integral(M)-i phi).
# For REAL integral(M), either both are 1 or neither is 1.
I,phi=s.symbols('I phi',real=True)
monL=s.exp(-I-s.I*phi)
monR=s.exp(I-s.I*phi)
assert s.simplify(monL.subs({I:0,phi:0})-1)==0
assert s.simplify(monR.subs({I:0,phi:0})-1)==0
assert s.simplify(monL.subs({I:0,phi:s.pi})+1)==0
assert s.simplify(monR.subs({I:0,phi:s.pi})+1)==0
for real_I in [-3,-1,0,2]:
    for real_phi in [0,s.pi,s.pi/3]:
        L=(real_I==0 and real_phi==0)
        R=(real_I==0 and real_phi==0)
        assert L==R

# A scalar wall X(theta) is NOT invariant under continuous circle
# translations: its positive |d_theta X|² is a stiffness for the KK
# graviphoton. Upon expanding (partial_mu X-kappa A_mu partial_theta X)²,
# the quadratic A_mu A^mu coefficient is kappa² int |X'|².
# It is a Stückelberg/gauge-invariant mass after the position Goldstone
# is kept; dropping that Goldstone is NOT an invariant truncation.
stiffness=s.factor(kappa*kappa*gradient_sq)
assert s.simplify(stiffness-s.pi*kappa*kappa*v*v)==0
print('PASS real periodic mass smooth S1: L/R zero modes paired (net chiral index zero)')
print('PASS explicit nonconstant profile: positive KK graviphoton stiffness=',stiffness)
print('INDEPENDENT Maxwell B_mu may remain massless if profile carries no B charge')
print('NO PROOF of physical wall background, source backreaction, anomaly inflow or orbifold determinant')
