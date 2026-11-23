#!/usr/bin/env python3
"""KK-geometric radion plus explicitly added chameleon 4D EFT potential.

This potential is NOT derived by the pure 5D KK EH circle reduction. The
matter conformal factor A and electromagnetic factor Z are inherited from
existing DASHI KKSingleActionRadionPhysicalSteelman20261024.md.
Fixed magnetic B ensemble, linearized exponentials, positive minimum regime.
"""
import sympy as s
def main():
    phi,M,Lam,rhoe,u,lam=s.symbols('phi M Lam rhoe u lam',positive=True)
    beta=1/s.sqrt(6)
    assert s.simplify((beta*rhoe-s.sqrt(6)*u)/beta-(rhoe-6*u))==0
    V=Lam**5/phi+lam*phi/M
    root=s.sqrt(Lam**5*M/lam)
    assert s.simplify(s.diff(V,phi).subs(phi,root))==0
    m2=s.simplify(s.diff(V,phi,2).subs(phi,root))
    expected=2*lam**s.Rational(3,2)/(Lam**s.Rational(5,2)*M**s.Rational(3,2))
    assert s.simplify(m2-expected)==0
    assert s.simplify(s.diff(s.log(m2),lam)-s.Rational(3,2)/lam)==0
    rho=6000.;c=299792458.;mu0=1.25663706212e-6
    ub=1/(2*mu0)
    ratio=6*ub/(rho*c*c)
    assert 4e-15<ratio<5e-15
    mratio=(1-ratio)**.75
    assert 0<1-mratio<1e-14
    print('PASS KK-coupled chameleon analytic minimum and mass response')
    print('6u/(rho c²), B=1T, illustrative rho=6000kg/m³:',ratio)
    print('fractional change of scalar inverse length in this limit:',mratio-1)
    print('NOT 5D-derived stabilization, not measured bulk YBCO, not 2% gravity prediction')
    print('OPEN exact 5D parent, environmental BVP and torsion-balance/clock constraints')

if __name__=='__main__':main()
