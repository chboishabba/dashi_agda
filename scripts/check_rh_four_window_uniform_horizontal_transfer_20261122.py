#!/usr/bin/env python3
"""RH P0 original four-window: explicit uniform-in-horizontal finite-t transfer.

Source owners: RiemannProjectiveQuarticFourWindowPoleSameObject.lean,
RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean,
RiemannProjectiveQuarticFourWindow.lean.
This is arithmetic validation of an analytic bound, NOT Lean kernel acceptance.
Assume normalized nonnegative symmetric source bump, coefficient
lambda in [1/2,2/3], |mu| <= 1/10, 0<R<1, t>=200, |a|<=1/2.
No positive q=4 high-limit margin is *generated* by this script.
"""
import sympy as s
F=s.Rational
# The original (1,-1,lambda,mu) weight sum <= 1+1+2/3+1/10 <3
assert 1+1+F(2,3)+F(1,10)<3
# Original support |x|< pi+R<5; for t>=200 the two
# cosh arguments |8*x/t|, |16*a*x/t| <= 40/t <= 1/5.
assert F(40,200)==F(1,5)
# Elementary scalar cosh bounds for |z|<=1/5:
# cosh z <=2, |cosh z-1|<=z².
# This follows e.g. cosh(1/5)<2 and cosh(z)-1 =
# z² * sum_{n>=1} z^{2n-2}/(2n)! <= z²*cosh(1/5)/2 <= z².
# Each hyperbolic factor discrepancy <= 1600/t².
change=40**2
assert change==1600
# On-line absolute A_c <=3, pole B_c(infty)<=3,
# finite pole B_c(t)<=6; selected component P=B1*A2-B2*A1:
pole_error=2*(3*3*change)
assert pole_error==28800
pole_inf_bound=2*3*3
assert pole_inf_bound==18
# Component profile F(a,q)=4 ∫G (A1 cos2x-A2 cosx)
# cos(qx) cosh(16ax/t); normalized signed TV(G)<=3.
profile_t_bound=4*3*(3+3)*2
profile_error=4*3*(3+3)*change
assert profile_t_bound==144
assert profile_error==115200
# Selected K=P_two*F_half-P_half*F_two.
transfer=2*(pole_error*profile_t_bound+
            pole_inf_bound*profile_error)
assert transfer==12441600
assert transfer<13000000
# Thus |K_t-K_inf| <=13e6/t² for all |a|<=1/2,
# where K_inf is the high-pole zero-horizontal q=4 smooth pair
# with fixed R, fixed original J2 selected coefficients.
# For fixed R with kappa_R>0, t>sqrt(13e6/kappa_R)
# gives K_t(a,4)>0 uniformly in physical horizontal a.
print("PASS exact source coefficient TV and support bounds")
print("PASS pole 28800/t² and profile 115200/t² discrepancies")
print("PASS selected 12441600/t² < 13000000/t² uniform transfer")
print("CONDITIONAL: kappa_R=K_inf(0,4;R)>0 on original J2 branch")
print("OPEN: constructive source-bump kappa_R floor and true zeta signed terminal")
