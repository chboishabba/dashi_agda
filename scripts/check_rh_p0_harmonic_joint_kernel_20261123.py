#!/usr/bin/env python3
"""RH P0: source-aligned two-variable signed quartic kernel/rigorous sign sectors.

Same-source owners (Lean main): signedNormalizedPairKernel_eq_jointJet,
signedHorizontalQuadraticKernel_secondDeriv_zero, combinedProfile_taperMass_le_explicit,
quarticFourCombinedProfileMassBound_lt_5184, combinedProfile_support_abs_le_pi_add_one,
and signed target strength floor. Numerical bump is an independent smooth fixture,
NOT the existentially selected original W(t). No RH/GRH claim or kernel receipt.
"""
from fractions import Fraction as F
import sympy as S
import mpmath as mp

q, alpha, v, T, M0, M2, M4 = S.symbols('q alpha v T M0 M2 M4', real=True)
z = q + S.I*alpha
p4 = S.expand(S.re(z**4))
assert S.expand(p4) == q**4 - 6*q**2*alpha**2 + alpha**4
jet = M0 - M2*S.re(z**2)/2 + M4*p4/24
assert S.simplify(jet.subs({M2:0,M4:-4*T})-(M0-T*p4/6)) == 0
assert S.simplify(S.diff(jet,q,2)+S.diff(jet,alpha,2)) == 0
assert p4.subs(q,alpha) == -4*alpha**4
assert p4.subs(alpha,0) == q**4
print('PASS exact source J2/M4 polynomial and 2D harmonicity')

# The genuine selected witness has ||P||_1 < 5184 and support |v| < pi+1 < 5
# (Lean QuantitativeBand, for t>=200). Source strength >= 7*pi^4/1600.
# For real alpha and q, cos((q+i*alpha)*v) Taylor after degree 4 has
# |E6| <= ||P||_1 * L^6 * (alpha^2+q^2)^3 * exp(L*|alpha|)/720.
# At 0<h<=10^-4, L<5 and exp(5h)<2, so use purely rational bounds.
h = F(1, 10000)
floor = F(7*3**4,1600)  # pi > 3
maxmass = F(5184)
maxsupport = F(5)
axis_error = maxmass*maxsupport**6*2*h**6/F(720)
diag_error = maxmass*maxsupport**6*2*(2*h*h)**3/F(720)
axis_margin = floor*h**4/6-axis_error
diag_margin = 2*floor*h**4/3-diag_error
assert axis_margin > 0 and diag_margin > 0
assert axis_margin/h**4 == F(909,16000)
assert diag_margin/h**4 == F(873,4000)
# Strict |alpha|=h,q=h vs |alpha|=0,q=h, relative to same K(0,0).
print('PASS exact rational sharp sign bounds for all selected W:')
print('  K(h,h)-K(0,0) >=', diag_margin/h**4, '*h^4 > 0')
print('  K(0,h)-K(0,0) <= -', axis_margin/h**4, '*h^4 < 0')

# Physical alpha = 16*(beta-1/2)/t, |beta-1/2|<=1/2.
# For t>=80000 this is <=10^-4; the diagonal q=|alpha| corresponds
# to |gamma-t|=|beta-1/2|, not an assumed actual zeta zero.
assert F(8,80000)==h
print('PASS physical horizontal strip becomes small at t>=80000')

# Independent exactly C-infinity, compact, even signed fixture:
# b(v) = exp(-1/(1-v^2)) for |v|<1, P(v)=-b''''(v).
# Its transform K(alpha,q)=-Re[(q+i alpha)^4 B(q+i alpha)].
# Integration by parts gives M0=M2=0 and M4=-24*int b <0.
mp.mp.dps = 45
def bump(x):
    return mp.exp(-1/(1-x*x)) if abs(x) < 1 else mp.mpf(0)
def B(z):
    return 2*mp.quad(lambda x:bump(x)*mp.cos(z*x), [0, 0.5, 0.9, 1])
def kernel(a,q):
    z=mp.mpc(q,a)
    return mp.re(-z**4*B(z))
for small in ('0.1','0.01','0.0001'):
    a = mp.mpf(small)
    k0 = kernel(0,a)
    kd = kernel(a,a)
    assert k0 < 0 < kd
    assert abs(k0/(-a**4) - B(0)) < mp.mpf('0.005')
    assert abs(kd/(4*a**4)-B(0)) < mp.mpf('0.005')
    print('PASS compact C-infinity P=-b4 fixture h=',small,
          'axis/h4=',mp.nstr(k0/a**4,10),'diag/h4=',mp.nstr(kd/a**4,10))
print('OPEN: true zeros at these q, actual weighted zero-minus-mu, post-sixth slack and strict P0 terminal')
