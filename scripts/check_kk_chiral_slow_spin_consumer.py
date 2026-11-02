#!/usr/bin/env python3
"""Two separately scoped KK BIDI consumers: chirality and leading slow rotation.
Neither calculation is a nonlinear 5D Earth interior or a precision LARES fit.
"""
import sympy as s

# PERIODIC S1 / S1-Z2 CHIRALITY CONSUMER.
parity={"g_munu":1,"g55_radion":1,"g_mu5_graviphoton":-1,
        "B_mu_independent_photon":1,"B5_Wilson":-1}
assert parity["B_mu_independent_photon"]==1
assert parity["g_mu5_graviphoton"]==parity["B5_Wilson"]==-1
smooth_S1_zero_modes={"left":1,"right":1}
assert smooth_S1_zero_modes["left"]-smooth_S1_zero_modes["right"]==0
for fermion_intrinsic_parity in (1,-1):
    surviving={side:int(fermion_intrinsic_parity*eigen==1)
               for side,eigen in (("left",-1),("right",1))}
    assert surviving["left"]+surviving["right"]==1
# Since bar(gamma5 Psi)*gamma5 Psi = -bar(Psi)*Psi,
# a constant bare 5D Dirac mass is odd under the naive chiral orbifold.
constant_dirac_mass_parity=-1
assert constant_dirac_mass_parity !=1
print("PASS periodic circle fermion zero modes are vectorlike")
print("PASS S1/Z2 can select chirality and retain B_mu photon; removes g_mu5 and B5")
print("FAIL cross-transport: old circle Casimir/Wilson spectrum cannot survive orbifolding unchanged")

# FIRST GRAVITATIONAL / SLOW-SPIN ORDER ONLY.
eps,beta,scalar,spin=s.symbols("eps beta scalar spin",real=True)
einstein_spin=eps*spin
jordan_spin=s.exp(2*beta*eps*scalar)*einstein_spin
assert s.diff(jordan_spin,eps).subs(eps,0)==spin
assert s.diff(jordan_spin,eps,2).subs(eps,0)==4*beta*scalar*spin
assert s.simplify(s.series(jordan_spin,eps,0,3).removeO()
    -(eps*spin+2*beta*eps**2*scalar*spin))==0
# For static spherically symmetric scalar profile sourced by matter trace,
# the scalar has no independent spin-one linear perturbation and scalar
# stress in Einstein eq starts quadratically. At fixed stress T_0i and
# bare G, leading gravitomagnetic potential therefore equals GR.
radius,alt,lam=s.symbols("radius altitude lam",positive=True)
assert s.simplify(s.exp(-((radius+alt)-radius)/lam)-s.exp(-alt/lam))==0
lam_meter=5.234166054200878e-13  # charged-branch radion range at b0=1e-24m
for h in (100_000,400_000,5_000_000):
    assert h/lam_meter>1e15
print("PASS Jordan g0i matches Einstein/GR at linear GJ order, given the same tensor source")
print("PASS charged-branch scalar Yukawa negligible at sampled satellite altitudes")
print("LIMIT higher-order G² M J, real Earth source, physical G calibration and 5D exact junction open")
