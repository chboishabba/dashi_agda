#!/usr/bin/env python3
"""Minimal KK radion magnetic-source scale vs a specified static slab.

Source prior art: DASHI KKSingleActionRadionPhysicalSteelman20261024.md,
check_kk_radion_reduced_action.py; KK circle reduction is not original here.
This model fixes the applied magnetic field (the source ensemble matters).
Not a physical demonstration of gravity screening or an all-KK no-go.
"""
import sympy as s
G=s.Rational(667430,10**16)
c=s.Integer(299792458)
mu0=s.Rational(125663706212,10**17)
def main():
    v,M,u,m0=s.symbols('v M u m0',positive=True,real=True)
    Z=s.exp(s.sqrt(6)*v/M)
    V=m0*m0*v*v/2+u*Z
    assert s.simplify(s.diff(V,v,2).subs(v,0)-m0*m0-6*u/M**2)==0
    beta=s.simplify(M*s.diff(s.log(s.exp(-v/(s.sqrt(6)*M))),v))
    assert s.simplify(2*beta**2-s.Rational(1,3))==0
    B=s.symbols('B',positive=True)
    ub=B**2/(2*mu0)
    k2=s.simplify(6*(8*s.pi*G/c**4)*ub)
    assert s.simplify(k2-24*s.pi*G*B**2/(mu0*c**4))==0
    k1=float(s.sqrt(k2.subs(B,1)))
    assert 6e-19<k1<8e-19
    d=s.Rational(1,100);f=s.Rational(2,25);att=1-f
    # Single exponential IS NOT a full slab boundary-value solution.
    kexp=s.log(1/att)/d
    # 1D phi''=k²phi; fixed lower potential and upper Robin phi'=-mout phi.
    # In limit mout->0 amplitude transmission =sech(k*d).
    kr=s.acosh(1/att)/d
    assert s.simplify(1/s.cosh(kr*d)-att)==0
    assert float(kr)>float(kexp)>8
    ratio=float(kr)/k1
    assert ratio>1e19
    Breq=float(s.sqrt(s.solve(s.Eq(k2,kr**2),B**2)[0]))
    assert Breq>1e19
    print('PASS exact fixed-applied-B KK mass², E-frame matter coupling, static slab')
    print('1 T magnetic energy density J/m³:',float(ub.subs(B,1)))
    print('1 T induced inverse length m^-1:',k1)
    print('8% scalar-only attenuation across 1cm: ideal exponential k:',float(kexp))
    print('specified Robin static slab k:',float(kr))
    print('inverse-length ratio k_required/k_from_1T:',ratio)
    print('required B under this exact minimal mechanism, tesla:',Breq)
    print('OPEN full 5D action stabilization, Earth exterior BVP, screened scalar and measured REBCO')

if __name__=='__main__':main()
