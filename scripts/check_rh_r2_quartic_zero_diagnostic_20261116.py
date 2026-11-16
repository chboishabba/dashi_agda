#!/usr/bin/env python3
"""RH R2: exact completed quartic sign geometry + numerical zero controls.

This is NOT a computation of the literal selected Lean W, FarExact, or R2 gap.
Requires sympy and mpmath. Execute: python scripts/check_rh_r2_quartic_zero_diagnostic_20261116.py
"""
import json
import sympy as s
import mpmath as mp

a,q,r=s.symbols("a q r",real=True)
P=s.expand(a*a*q*q-(a**4+q**4)/6)
B=s.Rational(7,4320)*(a**6+q**6)+s.Rational(5,192)*a**2*q**4+s.Rational(1,48)*a**4*q**2
lo,hi=3-2*s.sqrt(2),3+2*s.sqrt(2)
assert s.factor(6*P.subs(q*q,r*a*a))==-a**4*(r**2-6*r+1)
assert s.simplify(lo+hi-6)==0 and s.simplify(lo*hi-1)==0
assert P.subs({a:1,q:0})==-s.Rational(1,6)
assert P.subs({a:1,q:1})==s.Rational(2,3)
assert P.subs({a:0,q:1})==-s.Rational(1,6)
assert s.expand(B).coeff(a,6)==s.Rational(7,4320)
assert s.expand(B).coeff(q,6)==s.Rational(7,4320)
assert s.expand(B).coeff(a,2).coeff(q,4)==s.Rational(5,192)
assert s.expand(B).coeff(a,4).coeff(q,2)==s.Rational(1,48)
x,y,l=s.symbols("x y l",real=True)
assert s.expand(P.subs({a:l*x,q:l*y})-l**4*P.subs({a:x,q:y}))==0
assert s.expand(B.subs({a:l*x,q:l*y})-l**6*B.subs({a:x,q:y}))==0

# The full K=S*P+R has |R|<=M*B only on the certified local domain.
# Thus S*P>M*B certifies positive K, and S*P< -M*B negative K.
# No values of S, M, W, or the local domain are invented here.
mp.mp.dps=45
zeros=[]
for k in range(1,33):
    z=mp.zetazero(k)
    zeros.append({"index":k,"ordinate":mp.nstr(mp.im(z),24),
                  "computed_real_part":mp.nstr(mp.re(z),20),
                  "zeta_residual":mp.nstr(abs(mp.zeta(z)),5)})
assert all(abs(mp.mpf(z["computed_real_part"])-mp.mpf("0.5"))<mp.mpf("1e-25") for z in zeros)
print(json.dumps({
    "status":"PASS",
    "quartic_positive_ratio":[str(lo),str(hi)],
    "old_cone_not_full_quartic_positive":{"alpha":1,"q":0,"P":"-1/6"},
    "sixth_remainder_coefficients":["7/4320","5/192","1/48"],
    "numerical_zeros_only":zeros,
    "literal_selected_W_instantiated":False,
    "literal_FarExact_evaluated":False,
    "full_kernel_sign_certificates":0,
    "uniform_cofinal_gap_proved":False,
    "R2_closed":False
},indent=2))
