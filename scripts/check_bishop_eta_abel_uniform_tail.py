#!/usr/bin/env python3
"""Exact finite Abel telescoping and diagnostics for ORIGINAL Bishop eta tail.

For s with sigma=Re s>0, a_n=n^-s and A_j=sum_{k=0}^j(-1)^k in {0,1}:
  sum_{j=0}^(m-1) (-1)^j a_(N+j)
    = A_(m-1)*a_(N+m-1)
      + sum_{j=0}^(m-2) A_j*(a_(N+j)-a_(N+j+1)).
Hence |block| <= N^-sigma*(1+|s|/sigma), using
a_n-a_(n+1) = s*int_n^(n+1) x^(-s-1) dx.
On compact sigma>=delta>0 and |s|<=M, the uniform tail is
<= (1+M/delta) N^-delta. The original Bishop carrier-specific
complex logarithm, exponentiation, integral and SeriesOf weld
remain open; numeric checks do not establish those.
"""
from fractions import Fraction
from itertools import product
import cmath, json, math

def finite_abel(a):
    lhs=sum(((-1)**i*a[i] for i in range(len(a))),0)
    if not a:return lhs,0
    rhs=(len(a)%2)*a[-1]+sum((a[i]-a[i+1] for i in range(0,len(a)-1,2)),0)
    return lhs,rhs

def check():
    exact=0
    for n in range(9):
        for seq in product((Fraction(-3,2),Fraction(0),Fraction(2,3)),repeat=n):
            assert finite_abel(seq)[0]==finite_abel(seq)[1]
            exact+=1
    numerical=0
    worst=0.
    for sigma in (0.15,0.5,1.0,1.6):
        for y in (-5.,0.,0.5,6.75):
            s=complex(sigma,y)
            for N in (2,5,13,41):
                for m in (1,2,7,29,80):
                    block=sum(((-1)**k)*cmath.exp(-s*math.log(N+k))
                              for k in range(m))
                    B=(1+abs(s)/sigma)*N**(-sigma)
                    ratio=abs(block)/B
                    assert ratio<=1+1e-10
                    worst=max(worst,ratio)
                    numerical+=1
    return {"result":"PASS","exact_rational_Abel_cases":exact,
            "complex_eta_numeric_diagnostics":numerical,
            "max_observed_bound_ratio":worst,
            "claimed_uniform_majorant":"(1+M/delta)*N^(-delta)",
            "Bishop_original_NatLog_weld":False,
            "Bishop_original_expC_trig_add":False,
            "Bishop_actual_uniform_eta_Agda_proved":False,
            "kernel_receipt":False}
if __name__=="__main__":
    print(json.dumps(check(),indent=2))
