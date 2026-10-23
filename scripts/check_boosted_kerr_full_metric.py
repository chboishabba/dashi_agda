#!/usr/bin/env python3
"""Boosted Kerr KK Einstein-frame metric: leading-spin shift and static orbital frequency.
Geometric units; neutral Einstein-frame test-particle coupling assumed.
Not a full nodal perturbation or Earth-interior model.
"""
import sympy as s
from scipy.integrate import quad
from math import sinh,cos,pi
M,r,q,J=s.symbols('M r q J',positive=True, real=True)
H=1+2*M*q/r
gtt=-(1-2*M/r)/s.sqrt(H)
gphiphi=r*r*s.sqrt(H)
gtphi=-2*J/(r*s.sqrt(H))
shift=s.factor(-gtphi/gphiphi)
assert s.simplify(shift-2*J/(r**3*H))==0
circular=s.simplify(-s.diff(gtt,r)/s.diff(gphiphi,r))
x=s.symbols('x', positive=True)
series=s.series((circular/(M*(1+q/2)/r**3)).subs(M,x*r),x,0,2)
print('exact local frame dragging:',shift)
print('static circular Omega squared:',circular)
print('ratio to Newtonian M4 circular Omega squared:',series)
def average(a,e,alpha):
    mg=3.986004418e14/299792458.**2
    qq=sinh(alpha)**2
    den=quad(lambda E:(1-e*cos(E))**(-2),0,2*pi,epsrel=1e-12)[0]
    num=quad(lambda E:(1-e*cos(E))**(-2)/(1+2*mg*qq/(a*(1-e*cos(E)))),0,2*pi,epsrel=1e-12)[0]
    ratio=num/den
    approx=1-2*mg*qq/a*(1+e*e/2)/(1-e*e)
    assert abs(ratio-approx)<1e-14
    return ratio
for a,e in [(7820e3,.001),(12270e3,.0045)]:
    for alpha in [0,.3,1]:
        ratio=average(a,e,alpha)
        print(f'a={a/1000:g}km alpha={alpha} ratio={ratio:.15f} delta={ratio-1:+.5e}')
print('PASS metric shift, equatorial circular frequency, weak-field orbit-average proxy')
print('WARNING excludes modifications of full orbital plane dynamics and physical source')
