"""F8 W2: high-frequency physical material Schur absorption and low-k
Ward momentum divided difference. Conditional on existing normal trace,
constraint-compatible geometry, and actual propagated source regularity.
"""
import sympy as s
from fractions import Fraction as F

def exact():
    b,t,k=s.symbols('b t k',positive=True);B=s.sqrt(1+b*b)
    cs=1/(3*B*B)
    # On t in [1,12], b=1/t; existing physical material energy.
    assert s.simplify(cs-s.Rational(1,3)/(1+b*b))==0
    assert s.simplify(cs.subs(b,1)-s.Rational(1,6))==0
    assert s.simplify(cs.subs(b,s.Rational(1,12))-s.Rational(48,145))==0
    # Conservative comparison: actual FRW E_M=(cs rho²+P²)/2 via q=-tP.\n    # Since b<=1 this also bounds (cs rho²+b² P²)/2, giving\n    # the weaker rho²<=12E_M, P²<=288E_M.
    assert s.simplify(2/(s.Rational(1,6))-12)==0
    assert s.simplify(2/(s.Rational(1,144))-288)==0
    # |rho+3P/(ik)|² <= 2rho² +18 P²/k²
    # <= (24+5184/k²) E_M for k>=1.
    C=s.Rational(24)+s.Rational(5184)/k**2
    assert s.expand(C-2*12-18*288/k**2)==0
    # Time-dependent conservative bound; the new material_momentum_frame_weld\n    # establishes sharper C=24+36/k² for the ACTUAL physical momentum:
    # Qmaterial² <= (24 + 36*t²/k²) E_M.
    Cphysical=24+36*t*t/k**2
    assert s.simplify(Cphysical.subs(t,12)-C)==0
    # Existing collar trace controls |Z(0)|²<=2 E_Z/lambda,
    # so cross <=sqrt(2*t^6*Cphysical/lambda)*sqrt(E_Z E_M).
    # For lambda>=2*t^6*Cphysical the cross <=(E_Z+E_M)/2.
    K=2*12**6*25
    assert K==149299200
    assert F(36*12**2,K*K)<1
    assert F(2*12**6*25,K)==1
    assert F(2*12**6*25,K+1)<1
    # Conditional bound: for every k>=K, lambda=sqrt(1+k²)>=k>=K.
    # The low/mid band is NOT proved coercive by this argument.
    z,em,lam=s.symbols('z em lam',nonnegative=True)
    assert s.expand((z+em)/2-s.sqrt(z*em)) != 0
    assert s.simplify(((s.sqrt(z)-s.sqrt(em))**2)/2-(z+em)/2+s.sqrt(z*em))==0
    # Zero-mode and regularized momentum: M(k)=k integral_0^1 M'(theta*k)dtheta.
    a,c,m0,theta=s.symbols('a c m0 theta',real=True)
    M=k*(a+c*k*k)
    quotient=s.integrate(s.diff(M,k).subs(k,theta*k),(theta,0,1))/s.I
    assert s.simplify(M/(s.I*k)-quotient)==0
    assert s.simplify(s.limit(M/(s.I*k),k,0,dir='+')+s.I*a)==0
    # Zero mode alone is not enough if radial differentiability is unavailable.
    bad=m0+k*(a+c*k*k)
    assert s.limit(s.Abs(bad/(s.I*k)).subs({m0:1,a:1,c:1}),k,0,dir='+')==s.oo
    print('PASS high-frequency t<=12 Schur threshold K=',K,'and low-k derivative regularization; mid-band and geometric trace open')

if __name__=='__main__':exact()
