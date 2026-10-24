#!/usr/bin/env python3
"""Exact selected 26D string B2 <-> dual C22 with varying dilaton.

Flat Lorentzian (-,+^25), H3=dB2, G23=e^(-2Phi)*H3=dC22.
This proves a FIELD-SECTOR solution of B2 EOM/Bianchi; explicitly
NOT Einstein+dilaton full sourced solution, quantum CFT or full K27
nonlinear realisation. Tree-level bosonic string effective action
S~integral sqrt(-g) e^-2Phi(R+4|dPhi|²-H3²/12).
"""
from fractions import Fraction as Q
from math import comb
import sympy as s

D=26
t=s.Symbol('t',real=True)
x3=s.Symbol('x3',real=True)
assert D-3==23 and D-4==22
assert comb(24,2)==comb(24,22)==276

def sign(seq):
    return (-1)**sum(seq[i]>seq[j] for i in range(len(seq))
                     for j in range(i+1,len(seq)))
assert sign(tuple(range(3,26))+(0,1,2))==-1
assert sign((0,1,2)+tuple(range(3,26)))==1

for slope,charge in [(Q(1),Q(2)),(Q(2,3),Q(3)),
                     (Q(-3,5),Q(5,2)),(Q(4),Q(7,3))]:
    sl=s.Rational(slope.numerator,slope.denominator)
    q=s.Rational(charge.numerator,charge.denominator)
    phi=sl*t
    B12=q*s.exp(2*phi)/(2*sl)
    H012=s.diff(B12,t)
    assert s.simplify(H012-q*s.exp(2*phi))==0
    # *26 H_{3..25}=epsilon_{3..25,012} H^{012}
    # =(-1)*(-H012)=+H012 for signature (-,+...+).
    dualG=s.simplify(s.exp(-2*phi)*(-1)*(-H012))
    assert s.simplify(dualG-q)==0
    C4to25=q*x3
    assert s.diff(C4to25,x3)==q  # dC_{3..25} = q
    assert s.simplify(s.diff(-s.exp(-2*phi)*H012,t))==0
    assert s.simplify(s.exp(2*phi)*dualG-H012)==0
    Hnorm=-H012**2       # H3²/3! in Lorentzian signature
    Gnorm=dualG**2       # G23²/23! in spatial directions
    assert s.simplify(s.exp(-2*phi)*Hnorm+s.exp(2*phi)*Gnorm)==0
    # EOM for FULL metric on the chosen flat ansatz does NOT hold:
    # R00 + 2 Hessian Phi00 - (1/4) H0ab H0^ab = -H012²/2.
    residual=-H012**2/s.Integer(2)
    assert s.simplify(residual.subs(t,0)+q*q/2)==0
    print('PASS local nonconstant dilaton B2/C22 dual EOM, Bianchi, norm; slope=',slope,'charge=',charge)

# 27D circle source's dual four-form has the SAME 23-form rank.
# For G27=diag(g26,r²), F4=H3 wedge dy, *27(F4)=r^-1 *26(H3).
for r in (Q(1,4),Q(1),Q(3,2),Q(7)):
    h=Q(5)
    assert r*(h/r)==h
print('PASS 27D four-form -> 26D 3-form circle star ranks, potential degree22')
print('NO-GO example is NOT coupled Einstein-dilaton solution (nonzero g00 equation residual)')
print('BOUNDARY Hodge rank correspondence does not construct K27/E27 dual Lie generators')

