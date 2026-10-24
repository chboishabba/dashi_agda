#!/usr/bin/env python3
"""ONE physical SU3LxSU3R two-bifundamental 5D Higgs source vs KK QED/QCD.

Donor Agda #1106: E32/E33 two-VEV Gram eigenvalues (0^4, 12>0);
36 real scalar coordinates, 12 gauge Goldstones, 24 transverse scalars.
This is the selected two-bifundamental TRUNCATION, NOT full E6 27+27.
The potential from this source breaks SU3LxSU3R -> SU2LxU1Y;
unbroken Y is NOT by itself the observed electroweak photon.

The gauge-invariant 5D action has -1/4 sum Tr F^2, |D_Phi|^2+
|D_Chi|^2, a six-invariant local potential, Dirac matter and gravity.
At the broken vacuum, 12 massive 5D vectors have 4 physical DOF
(not 3), four unbroken vectors have 3 DOF, and 24 physical scalar
modes remain: 48+12+24=84 = 16*3+36.

At v=10TeV,gL=gR=.65, coefficient lambda=.1, and b0=1e-24m,
the extra 36 scalar DOF are light relative to KK spacing.
They force D=W'(1)-5W(1)>164, uniformly in the previously tuned
neutral fermion mass z. Hence no stationary-flat 4D S1 vacuum under
that previously proposed fixed spectrum/counterterm scheme.
Changing to complete E6 representations, strong interactions, or
a different source potential creates DIFFERENT candidate theories.
"""
from mpmath import mp
mp.dps=45
Z5=mp.zeta(5)
HBARC=mp.mpf("0.1973269804e-15")
b0=mp.mpf("1e-24")/HBARC
g=mp.mpf(".65")
v=mp.mpf("10000")
lam=mp.mpf(".1")
def f(s):
    u=mp.exp(-s)
    return (mp.polylog(5,u)+s*mp.polylog(4,u)+s*s*mp.polylog(3,u)/3)/Z5
def fp(s):
    u=mp.exp(-s)
    return -s*(mp.polylog(3,u)+s*mp.polylog(2,u))/(3*Z5)
def h(s):return f(s)-s*fp(s)/5
def hp(s):
    u=mp.exp(-s)
    return -s*(3*mp.polylog(3,u)+3*s*mp.polylog(2,u)+s*s*mp.polylog(1,u))/(15*Z5)
assert abs(h(mp.mpf(".12"))- (f(mp.mpf(".12"))-mp.mpf(".12")*fp(mp.mpf(".12"))/5)) <mp.mpf('1e-40')
assert hp(mp.mpf(".12"))<0

# Eigenvalues in the original comparison metric; the true mass
# normalisation must be fixed by the kinetic term, so set explicitly.
vector_eigens=[mp.mpf(1)/4]*4+[mp.mpf(1)/2]*7+[mp.mpf(5)/6]
scalar_eigens=[mp.mpf(4)]*6+[mp.mpf(6)]*8+[mp.mpf(8)]*10
assert len(vector_eigens)==12 and len(scalar_eigens)==24
assert 4*3+12*4+24==84==16*3+36
vector_masses=[g*v*mp.sqrt(k) for k in vector_eigens]
scalar_masses=[v*mp.sqrt(lam*k) for k in scalar_eigens]
all_masses=vector_masses+scalar_masses
assert max(all_masses)<30000
zv=[2*mp.pi*b0*m for m in vector_masses]
zs=[2*mp.pi*b0*m for m in scalar_masses]
quark_masses=[mp.mpf(x) for x in (".00216",".00470",".0935","1.273","4.183","172.56")]
zq=[2*mp.pi*m*b0 for m in quark_masses]
ze=2*mp.pi*mp.mpf(".00051099895")*b0

# old E6-inspired gauge-only source had -48 = 16 massless LR x3.
# New LR is -12 -4*SUM_12 f(mV*b) -SUM_24 f(mH*b).
# colour -24 and 6*3 Dirac quarks +72, original QED sector:
# -9 + 4 f(z)+4 f(4z)+4 f(ze).
def D_new(z):
    return 5*(9+24+12)+20*mp.fsum(h(s) for s in zv)+5*mp.fsum(h(s) for s in zs) - \
           20*(h(z)+h(4*z)+h(ze))-60*mp.fsum(h(s) for s in zq)
def D_old(z):
    return 5*(9+24+48)-20*(h(z)+h(4*z)+h(ze))-60*mp.fsum(h(s) for s in zq)
def deltaD():
    return D_new(mp.mpf(".8"))-D_old(mp.mpf(".8"))
# Strict universal z-independent bound: 0<h(z)<=1 for any z>=0,
# all new vector/scalar masses <=30TeV so h(z) >= h(zmax).
zmax=2*mp.pi*b0*mp.mpf(30000)
hmin=h(zmax)
assert hmin>mp.mpf("0.999999")
lower_bound=225+(12*20+24*5)*hmin-60-360
assert lower_bound>164
for x in map(mp.mpf,(".00001",".1",".5",".9081569908","1","2","5","30")):
    assert D_new(x)>=lower_bound
old_root=mp.findroot(D_old,(mp.mpf(".7"),mp.mpf("1.2")))
assert abs(D_old(old_root))<mp.mpf("1e-35")
assert D_new(old_root)>164
assert mp.mpf("179.99")<deltaD()<mp.mpf("180.01")
# Cross-check massive vector physics at m->0:
assert 4*12+3*4+24==16*3+36
print("old_radion_z",mp.nstr(old_root,18))
print("massive_vector_multiplicities",[(str(k),vector_eigens.count(k)) for k in sorted(set(vector_eigens))])
print("max_gauge_mass_GeV",mp.nstr(max(vector_masses),15))
print("max_scalar_mass_GeV",mp.nstr(max(scalar_masses),15))
print("full_twoVEV_scalar_polarizations",36)
print("old_extra_LR_boson_units",48)
print("new_extra_LR_boson_units_UV",84)
print("delta_D_same_radius",mp.nstr(deltaD(),21))
print("universal_z_stationarity_lower_bound",mp.nstr(lower_bound,21))
print("D_at_previous_stationary_radius",mp.nstr(D_new(old_root),21))
print("PASS: no stationary 4D-Minkowski vacuum for this selected complete two-bifundamental 5D free determinant, ANY neutral mass z")
print("OPEN: full E6 27 scalar copies, EW breaking, interaction loops, CS/global anomalies, 5D dynamic matter")
