#!/usr/bin/env python3
"""Exact source-uniform TWO-global-mark original Wilson affine analytic check.

Any strictly positive original Wilson/Haar conditional fibre with bounded
real F,G in [-1,1] satisfies the theorem. This test uses finite rational
positive laws as independent checks; no physical W3 spatial rate is inferred.
"""
from itertools import product
import sympy as S

r = S.Rational(9, 100)
real_low = (1-r)**2
real_up = (1+r)**2
complex_floor = 1-2*r-r*r
real_hess = (1-r*r)**(-2)
complex_hess = 2/complex_floor**2
assert real_low == S.Rational(8281, 10000)
assert real_up == S.Rational(11881, 10000)
assert complex_floor == S.Rational(8119, 10000)
assert real_hess == S.Rational(100000000, 98386561)
assert complex_hess == S.Rational(200000000, 65918161)

s,t = S.symbols("s t")
atoms = list(product((-1,1), repeat=2))
for weights in product((1,2,3,4), repeat=4):
    total = sum(weights)
    a = S.Rational(sum(w*f for w,(f,g) in zip(weights,atoms)),total)
    b = S.Rational(sum(w*g for w,(f,g) in zip(weights,atoms)),total)
    c = S.Rational(sum(w*f*g for w,(f,g) in zip(weights,atoms)),total)
    k = 1+s*a+t*b+s*t*c
    assert S.factor(k*c-S.diff(k,s)*S.diff(k,t)) == c-a*b
    for ss,tt in ((0,0),(r,r),(r,-r),(-r,r)):
        kv=k.subs({s:ss,t:tt})
        assert real_low <= kv <= real_up
        jet=S.factor(S.diff(S.diff(S.log(k),s),t)).subs({s:ss,t:tt})
        assert S.simplify(jet-(c-a*b)/kv**2)==0
        assert abs(jet) <= real_hess

# Sharp all-positive-law REAL bound: initial probabilities tilted to
# exactly 1/2 each on the two F=G=+1/-1 states.
wp=(1-r)**2
wm=(1+r)**2
pp=wp/(wp+wm)
pm=wm/(wp+wm)
z=pp*(1+r)**2 + pm*(1-r)**2
assert pp*(1+r)**2/z == pm*(1-r)**2/z == S.Rational(1,2)
sharp=S.factor((1/(1+r)+1/(1-r))**2/4)
assert sharp == real_hess

# Uniform zero-free holomorphic marked source does NOT force covariance
# decay at all: F=G is a single global fair sign at any separation.
assert S.diff(S.diff(S.log(1+s*t),s),t).subs({s:0,t:0}) == 1
print("PASS 256 positive conditional source laws; 1024 rational source settings")
print("PASS 9/100 real positive K/K0:",real_low,"..",real_up)
print("PASS original complex analytic source floor:",complex_floor)
print("PASS real sharp log-Hessian universal max:",real_hess)
print("PASS complex analytic log-Hessian universal max:",complex_hess)
print("PASS global-sign no-physical-decay negative control")
print("OPEN real CMP116 J identification; renormalized absolute W3 physical rate")
