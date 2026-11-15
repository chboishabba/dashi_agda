#!/usr/bin/env python3
"""SAME proposed 5D SU3c x SU3L x SU3R x U1_B action spectrum gate.

Combines:
 #1106 two bifundamental 3x3 Higgs fields (36 real physical input),
 L/R broken gauge vectors (12 massive with FOUR 5D DOF, 4 unbroken
 with THREE), 24 physical Higgs amplitudes and 12 eaten Goldstones;
 #1241 soft-split 8 fundamental SU3c Dirac/complex-scalar pairs,
 gauge adjoint gauginos/scalars and original independent U1 QED;
 one NEW dynamical gauge-singlet real spurion X needed to supply a
 simple gauge-invariant local source for 3/4/9TeV mass splitting.
 
This is a conditional tree-level gauge-covariant EFT with selected 5D
source coefficients, NOT an exact E6 unified action or anomaly-safe SM.
5D X_5 has dimension 3/2; X4=sqrt(L0) X5. To produce X4=w4,
y5=y4 sqrt(L0), kappa5=kappa4 L0, lambda5=lambda4 L0.
This is the selected b0 normalization, not a claim those dimensionful
5D couplings are renormalizable.

At TeV scale all new masses are negligible vs b0^-1=197MeV*1e9.
The full paired+Higgs+spurion free determinant has a rigorous
STATIONARY-MINKOWSKI no-go for ANY neutral-stabilizer mass z
at fixed b0, phase0 and declared sources, even retuning bulk Lambda.
"""
from mpmath import mp
mp.dps=43
Z=mp.zeta(5)
b0=mp.mpf('1e-24')/mp.mpf('0.1973269804e-15')
L0=2*mp.pi*b0
w4=mp.mpf('1000')
lambda4=mp.mpf('.4')
y4=mp.mpf(1)
k4=mp.mpf(1)
w5=w4/mp.sqrt(L0)
y5=y4*mp.sqrt(L0)
k5=k4*L0
lambda5=lambda4*L0
assert abs(y5*w5-1000)<mp.mpf('1e-33')
assert abs(k5*w5*w5-1_000_000)<mp.mpf('1e-30')
mX=mp.sqrt(8*lambda4*w4*w4)
g=mp.mpf('.65');v=mp.mpf('10000');lam=mp.mpf('.1')
gv=[mp.mpf(1)/4]*4+[mp.mpf(1)/2]*7+[mp.mpf(5)/6]
hs=[mp.mpf(4)]*6+[mp.mpf(6)]*8+[mp.mpf(8)]*10
assert len(gv)==12 and len(hs)==24
zV=[2*mp.pi*b0*g*v*mp.sqrt(s) for s in gv]
zH=[2*mp.pi*b0*v*mp.sqrt(lam*s) for s in hs]
zspur=2*mp.pi*b0*mX
zS=2*mp.pi*b0*3000
zG=2*mp.pi*b0*4000
zEx=2*mp.pi*b0*9000
ze=2*mp.pi*b0*mp.mpf('.00051099895')
zq=[2*mp.pi*b0*mp.mpf(m) for m in
    ('.00216','.00470','.0935','1.273','4.183','172.56')]
def f(s):
    u=mp.exp(-s)
    return (mp.polylog(5,u)+s*mp.polylog(4,u)+s*s*mp.polylog(3,u)/3)/Z
def fp(s):
    u=mp.exp(-s)
    return -s*(mp.polylog(3,u)+s*mp.polylog(2,u))/(3*Z)
def h(s): return f(s)-s*fp(s)/5
# Original paired effective potential and reference b0 from previous cut.
# Exact same free spectral determinant at zero EM/colour phases:
def D_paired(z):
    return 5*(9-4*h(z)-4*h(4*z)-4*h(ze)) + \
      8*(15-15*h(zG)) + \
      60*mp.fsum(h(zS)-h(q) for q in zq) + \
      120*(h(zS)-h(zEx))
def D_LR():
    return 5*12 +20*mp.fsum(h(x) for x in zV)+5*mp.fsum(h(x) for x in zH)
def D_joint(z):
    return D_paired(z)+D_LR()+5*h(zspur)
z_old=mp.findroot(D_paired,(mp.mpf('.7'),mp.mpf('1.2')))
assert abs(D_paired(z_old))<mp.mpf('1e-30')
assert 4*3+12*4+24==16*3+36==84
assert 4*3+12*4+24+1==85
assert D_LR()>mp.mpf(419)
# Rigorous z-independent bound: all periodic h in (0,1]; three
# original neutral stabilizer positive h terms have at most 12
# dimensionless fermion units. The SU3 adjoint term >=0;
# exotic fermion-minus-boson term >=0 as 9000>3000 GeV;
# light quarks minus heavier scalar term bounded below by
# -360*(1-h(zS)), uniformly in the unknown neutral mass.
zmax=2*mp.pi*b0*30000
assert all(m<=zmax for m in zV+zH)
hmin=h(zmax)
bound_paired=-15-360*(1-h(zS))
bound_lr=60+360*hmin
bound_spurion=5*h(zspur)
universal_bound=bound_paired+bound_lr+bound_spurion
assert universal_bound>409
for z in map(mp.mpf,('.00001','.01','.1','.9','1','3','20')):
    assert D_joint(z)>universal_bound
# Minkowski tuning ell=-W(1) removes bulk constant but 5D pressure:
# p5=-c0*(W'-5W)/(2*pi*b0^5). Positive D gives negative p5.
c0=3*Z/(64*mp.pi**6)
p5=-c0*D_joint(z_old)/(2*mp.pi*b0**5)
assert p5<0
for name,value in (
 ('inverse_radius_GeV',1/b0),
 ('5d_spurion_vev_mass_dimension_3over2',w5),
 ('5d_yukawa_dimension_minus_half',y5),
 ('5d_quartic_portal_dimension_minus_one',k5),
 ('5d_spurion_quartic_dimension_minus_one',lambda5),
 ('physical_spurion_mass_GeV',mX),
 ('prior_paired_radion_z',z_old),
 ('LR_vector_and_Higgs_Casimir_D',D_LR()),
 ('additional_spurion_Casimir_D',5*h(zspur)),
 ('joint_D_at_old_radius',D_joint(z_old)),
 ('universal_lower_D_any_neutral_z',universal_bound),
 ('uncancelled_internal_pressure_GeV5',p5)):
    print(name,mp.nstr(value,18))
print('PASS same-reference-radius conditional source has no stationary Minkowski vacuum for ANY neutral stabilizer mass; bulk Lambda alone cannot repair')
print('FAIL identification of independent U1_B photon with the separate SU2LxU1Y electroweak residual photon without additional gauge mixing/breaking')
print('OPEN actual 5D quantum interactions/CS and quotient group, scalar background quantum stationarity, realistic chiral E6 matter, full 4-field global potential')
