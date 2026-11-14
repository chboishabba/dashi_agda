#!/usr/bin/env python3
"""Symbolic Rayleigh-Ritz bound on the exact Gielis continuum domain.

The H_0^1 trial function u(r,theta)=1-(r/r_m(theta))^2 has
energy integral[1+(r'/r)^2] and L2 norm²=(1/6)integral[r²].
Neither statement certifies a Cartesian finite-difference eigenvalue.
"""
from fractions import Fraction as Q
import sympy as s
import json

def theorem():
    t=s.symbols("t",real=True)
    integral=s.integrate(2*t**2/((1+t**2)*(2+t**2)**2),
                         (t,-s.oo,s.oo))
    assert s.simplify(
        integral-2*s.pi*(s.Rational(3,2)/s.sqrt(2)-1))==0
    out={}
    for m in (3,6,9):
        upper=s.simplify(3/s.sqrt(2)*(
          2+s.Rational(m*m,2)*(s.Rational(3,2)/s.sqrt(2)-1)))
        assert s.simplify(
          upper-(s.Rational(9*m*m,8)+(12-3*m*m)/(2*s.sqrt(2))))==0
        out[str(m)]={"rayleigh_upper_exact":str(upper),
                     "approx":float(upper)}
    assert Q(99,70)**2>2 and Q(7,5)**2<2
    # m=3: sqrt(2)<99/70 => 1/sqrt(2)>70/99.
    bound=Q(81,8)-Q(15,2)*Q(70,99)
    assert bound==Q(1273,264)
    assert float(out["3"]["approx"])<float(bound)
    return {
        "angular_integral":str(integral),
        "Rayleigh":out,
        "m3_continuum_lambda1_upper_rational_strict":str(bound),
        "m3_upper_decimal":float(bound),
        "method":"H_0^1 radial trial function and Rayleigh-Ritz",
        "certified_numeric_FD_error":False,
        "native_Agda_kernel_acceptance":False,
    }
if __name__=="__main__":
    print(json.dumps(theorem(),indent=2,sort_keys=True))
