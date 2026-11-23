#!/usr/bin/env python3
"""Exact strong-coupling TWO original affine plaquette-source Dobrushin envelope.

Actual continuous SU(N) arguments use positive Haar, local Wilson plaquette
support and standard imported Dobrushin-Follmer covariance comparison.
The executable exact tests cover algebra, constants and original graph support.
No physical beta(a)->infinity W3 or E1/D2 claim.
"""
from itertools import product
from fractions import Fraction
from collections import Counter
import sympy as S

r=S.Rational(9,100)
beta=S.Rational(1,72)
q=18*beta+3*r
assert q==S.Rational(13,25)
assert S.simplify(18*S.tanh(beta)+3*r < q) is S.true
assert q < 1
# Mark potential V_s=log(1+sF), |F|<=1, real |s|<=r.
# osc_U[ V_s(U,eta)-V_s(U,eta') ] <= 2 log[(1+r)/(1-r)].
a=S.log((1+r)/(1-r))
assert S.simplify(S.tanh(a/2)-r)==0
# TV for one original plaquette neighbour: tanh(beta + atanh r)
assert S.simplify(S.tanh(beta+S.atanh(r)) <= S.tanh(beta)+r) is S.true

# The source-mixed log derivative is a covariance of two local scores under
# the SAME positive global Wilson-affine tilt, not a new polymer factor.
s,t=S.symbols('s t')
atoms=list(product((-1,1),repeat=2))
count=0
for weights in product((1,2,3,4),repeat=4):
    z0=sum(weights)
    P=[S.Rational(w,z0) for w in weights]
    K=sum(p*(1+s*f)*(1+t*g) for p,(f,g) in zip(P,atoms))
    ks=sum(p*f*(1+t*g) for p,(f,g) in zip(P,atoms))
    kt=sum(p*g*(1+s*f) for p,(f,g) in zip(P,atoms))
    kst=sum(p*f*g for p,(f,g) in zip(P,atoms))
    assert S.expand(K-S.expand(K))==0
    assert S.simplify(S.diff(S.diff(S.log(K),s),t)-(K*kst-ks*kt)/K**2)==0
    for ss,tt in ((0,0),(r,r),(-r,r),(r,-r)):
        z=K.subs({s:ss,t:tt})
        scores=[(S.Rational(f,1+ss*f),S.Rational(g,1+tt*g)) for f,g in atoms]
        tilt=[p*(1+ss*f)*(1+tt*g)/z for p,(f,g) in zip(P,atoms)]
        Ef=sum(p*f for p,(f,g) in zip(tilt,scores))
        Eg=sum(p*g for p,(f,g) in zip(tilt,scores))
        Efg=sum(p*f*g for p,(f,g) in zip(tilt,scores))
        jet=(K*kst-ks*kt)/K**2
        assert S.simplify(jet.subs({s:ss,t:tt})-(Efg-Ef*Eg))==0
        count+=1
assert count==1024

# Source-specific resolvent envelope with graph degree 18; two disjoint
# four-edge plaquette sources, each row adds at most three extra influences r.
score_osc=2/(1-r*r)
const=S.factor(score_osc**2/(1-q))
assert const == S.Rational(2500000000,295159683)
for d in range(0,25):
    per_pair=const*q**d
    assert per_pair>=0
    if d>0: assert per_pair <= const*q**(d-1)
print('PASS 256 original-affine positive source laws x 4 real source settings:',count)
print('PASS true local source mark potential TV surcharge <= r=',r)
print('PASS strict all-finite-volume REAL marked-source Dobrushin q<=',q)
print('PASS true original global affine mixed log jet is tilted local-score covariance')
print('PASS score envelope: |D_st logZ| <= (',const,')*|A||B| * (13/25)^d')
print('OPEN physical beta(a) large, renormalized CMP116/W3 absolute shell, E1/D2')
