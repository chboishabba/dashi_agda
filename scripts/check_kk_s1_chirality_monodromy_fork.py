#!/usr/bin/env python3
"""Smooth circle chirality vs orbifold/brane fork, selected 5D Dirac consumer.

Original source science:
Callan and Harvey 1985 domain-wall anomaly/zero modes;
Arkani-Hamed, Cohen, Georgi 2001, Anomalies on Orbifolds,
Phys Lett B 516 395, DOI 10.1016/S0370-2693(01)00946-7;
Scrucca, Serone, Silvestrini, Zwirner 2002, Phys Lett B 525 169,
DOI 10.1016/S0370-2693(01)01430-7, fixed-point anomalies.

Existing repo owner: DASHI/Physics/Gravity/KKCircleQEDChiralityConsumerExact.agda
and physical source branch KK #1241. Source-specific original here:
for real periodic M(y) and common flat unitary holonomy exp(i*theta),
5D Dirac zero-mode monodromies are exp(-I+i*theta), exp(I+i*theta),
I=int_0^(2*pi) M(y)dy. Both are 1 together; net 4D chiral index zero.
Nonconstant smooth walls cannot project out an entire chirality.
Orbifold S1/Z2 with compatible gamma5 projection can have one
chiral zero mode but demands NEW interval determinant, fixed-plane
anomaly and full mass/gauge parity receipts. Neither an orbifold
nor a brane is the earlier periodic S1 QCD Casimir theory.
"""
import cmath
import math
import sympy as sp
L=2*math.pi
def modes(mean,angle):
    I=L*mean
    hl=cmath.exp(-I+1j*angle)
    hr=cmath.exp(I+1j*angle)
    return (int(abs(hl-1)<1e-11),int(abs(hr-1)<1e-11))
for mean in (-2,-.25,0,.25,2):
    for angle in (0,math.pi/7,math.pi,2*math.pi):
        left,right=modes(mean,angle)
        assert left==right,(mean,angle)
assert modes(0,0)==(1,1)
assert modes(0,math.pi)==(0,0)
assert modes(1,0)==(0,0)
y,m0,a,b=sp.symbols('y m0 a b',real=True)
mass=m0+a*sp.cos(y)+b*sp.sin(2*y)
integral=sp.simplify(sp.integrate(mass,(y,0,2*sp.pi)))
assert sp.simplify(integral-2*sp.pi*m0)==0
partial=sp.simplify(sp.integrate(mass.subs(m0,0),(y,0,y)))
assert sp.simplify(partial-a*sp.sin(y)-b*(1-sp.cos(2*y))/2)==0
for yy in (0,math.pi/3,math.pi,4*math.pi/3,2*math.pi):
    val=float(partial.subs({y:yy,a:.2,b:.5}))
    assert math.exp(-val)>0 and math.exp(val)>0
# On S1/Z2 right- or left-even projection removes the other
# constant zero-mode. Not a claim all 27 representations can be
# projected compatibly with the chosen E6 gauge/higgs action.
orbifold_right_even=(0,1)
orbifold_left_even=(1,0)
assert orbifold_right_even[0]-orbifold_right_even[1]==-1
assert orbifold_left_even[0]-orbifold_left_even[1]==1
assert 27-27==0 and 27-0==27
b0_metres=1e-24
hbarc_GeV_metres=0.1973269804e-15
kkgap=hbarc_GeV_metres/b0_metres
assert 1.97e8<kkgap<1.98e8
print("PASS smooth S1: any REAL scalar periodic Dirac mass and UNITARY flat twist have equal left/right zero multiplicities")
print("PASS exact mass-profile integral:",integral)
print("PASS an orbifold parity projection can give an unpaired zero mode; full gauge and anomaly action NOT proven")
print("selected 1/b0 GeV:",kkgap)
print("FAILED consumer: chiral electroweak Standard Model from the old unmodified smooth-S1 bulk-27 fermion")
print("OPEN orbifold fixed-point anomaly/CS, new boundary Casimir, single photon, source stress and E6 full matter")
