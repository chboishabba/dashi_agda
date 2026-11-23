#!/usr/bin/env python3
"""Original Lean RH P0 BIDI marked-fourth: SHARP local geometry negative control.

Reads source identities (does not simulate zeros):
Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleBidiMarkedFourth.lean
  quarticSignedPoleFourthPhaseReal_eq_bidi_target_reflection
  literalLocalFourthPhaseMomentAt_eq_bidi_marked
  literalLocalCenteredFourthAngularAt_eq_bidi_discrepancy
Source excludes SameOrd(t); use only delta>0. Target at delta=0
remains separate and NOT counted in local off-ordinate mass.
Two abstract positive-integer-multiplicity reflection-symmetric clouds
are NOT actual zeta zeros. Test the sufficiency of M0/M2/reflection only.
"""
import sympy as s

h=s.symbols('h',positive=True)
A=s.Rational(5,2)*h  # arbitrary nonzero target beta-1/2
def p2(a,d):return a*a-d*d
def p4(a,d):return a**4-6*a*a*d*d+d**4
def cloud(ds):return [(a,d,1) for d in ds for a in (A,-A)]
def vertical(c,k):return s.factor(sum(m*d**k for a,d,m in c))
def bidi(c):
    m0=sum(m for a,d,m in c)
    m2=s.factor(sum(m*(p2(a-A,d)+p2(a+A,d)) for a,d,m in c))
    m4=s.factor(sum(m*(p4(a-A,d)+p4(a+A,d)) for a,d,m in c))
    d=s.factor(s.Rational(1,2)*m4-3*A*A*m2+5*A**4*m0)
    direct=s.factor(sum(m*p4(a,delta) for a,delta,m in c))
    assert s.simplify(d-direct)==0
    return m0,m2,m4,d
C=cloud([5*h,5*h])
D=cloud([h,7*h])
for X in (C,D):
    assert all(delta>0 and mult==1 and a in (A,-A)
               for a,delta,mult in X)
    assert len(X)==4
    for a,delta,mult in X:
        assert (-a,delta,mult) in X
    assert all(s.simplify(p4(a,d)-p4(-a,d))==0
               for a,d,_ in X)
assert vertical(C,0)==vertical(D,0)==4
assert vertical(C,2)==vertical(D,2)==100*h**2
assert vertical(C,4)==2500*h**4
assert vertical(D,4)==4804*h**4
assert bidi(C)[0:2]==bidi(D)[0:2]
assert bidi(C)[1]==-100*h**2
assert bidi(C)[2]==-7500*h**4
assert bidi(D)[2]==-2892*h**4
assert bidi(C)[3]==-s.Rational(4375,4)*h**4
assert bidi(D)[3]==s.Rational(4841,4)*h**4
assert bidi(D)[2]-bidi(C)[2]==4608*h**4
assert bidi(D)[3]-bidi(C)[3]==2304*h**4
# Sharp (vertical) moment cone: M2²/M0 <= M4 <= L² M2
# from Cauchy-Schwarz and support with nonnegative integer multiplicities.
m0,m2=vertical(C,0),vertical(C,2)
L=7*h
assert s.factor(m2**2/m0-vertical(C,4))==0
assert s.factor(L**2*m2-vertical(D,4))==96*h**4
# With FIXED |a|=A (only for these two clouds), angular Q is
# M4-6A²M2+A⁴M0. This interval crosses zero.
lower=s.factor(m2*m2/m0-6*A*A*m2+A**4*m0)
upper=s.factor(L*L*m2-6*A*A*m2+A**4*m0)
assert lower==-s.Rational(4375,4)*h**4
assert upper==s.Rational(5225,4)*h**4
assert lower<0 and upper>0
# Physical geometry: 0<h<1/10 ensures 0<A<1/2;
# if 7*h < eta*(t/16), all four synthetic offsets fit the
# local window but still do NOT satisfy the actual Zeros type.
assert s.Rational(5,2)*s.Rational(1,10)<s.Rational(1,2)
print('PASS source P2/P4 bidi reconstruction for every reflected event')
print('PASS both clouds: M0=4, vertical M2=100h², pair M2=-100h²')
print('PASS M4 vertical 2500 vs 4804 h⁴; pair M4 -7500 vs -2892 h⁴')
print('PASS zero fourth angular signs opposite:',bidi(C)[3],bidi(D)[3])
print('PASS sharp Jensen lower and support upper; cone crosses zero')
print('OPEN: actual Zeros occupancy, mu-background, signed far, local slack, strict G3')
