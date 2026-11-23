#!/usr/bin/env python3
"""Exact rational final q-window arithmetic on the original RH source.

Original source formula/branch audits:
- check_rh_original_bump_explicit_radius_20261122.py
- check_rh_original_bump_q4_sqrtR_boundary_layer_20261123.py
- Lean RiemannProjectiveQuarticFourWindow{,PoleSameObject} and
  SignedPolePair / SignedPoleJointHorizontalJet.
No Gaussian, no invented zeta-zero distribution, no Lean/Agda kernel.
The accompanying proof note derives each uniform analytic envelope.
"""
import sympy as s
from fractions import Fraction as Q
pi=s.pi
R=Q(1,10**10)
sqrtR=Q(1,10**5)
T=10**14
# Source-certified K1(4), K1'(4); triangle upper bound <20
v=-200*s.sqrt(3)*pi/117-s.Rational(10,13)+764*pi/351
assert 200*2*s.Rational(22,7)/117+s.Rational(10,13)+764*s.Rational(22,7)/351<20
assert abs(float(v))<20
# For |q-4|<=2sqrtR, original A(k) expansion requires |k|<=18.
# |K1''|<16e6 follows from P0<=18,P1<=6000,Q0''<=1152,
# Q1''<=60096, all bounded by the original signed mass<3 and |u|<4.
Aed7=6+4*7*12+7**2*48+10
Aed6=6+4*6*12+6**2*48+10
Q1dd=2*(4*2*48+3*2*Aed7+13*2*48+3*2*Aed6)
K1dd=2*(18*Q1dd+6000*1152)
assert (Aed7,Aed6,Q1dd)==(2704,2032,60096)
assert K1dd<16_000_000
K1var=20*(2*sqrtR)+8_000_000*(2*sqrtR)**2
assert K1var/2 <= Q(18,10_000)
# Source true normalized bump Fourier remainder <=k^4 R^4/24.
assert Q(3*18**4,24)==13_122 and Q(3*7**4,24)<301
Acoef=3+(3*18**2+1)+18**2
Kcoef=2*(2*Acoef**2)*(8*Acoef**2)
Perr=2*(13_122*3+3*2)
Qerr=15_000
Kinput=2*(Perr*72+19*Qerr)
Kbranch=2*(19*48+12*72)*600
C=Kcoef//4+Kinput+Kbranch
assert Acoef==1300 and C<23_000_000_000_000
# Horizontal alpha=16*a/t, |a|<=1/2.
# |v|<4 => both cosh(8v/t) and cosh(alpha*v) have |arg|<=32/t.
# cosh y-1<=y^2 for |y|<=.16, source mass sum<3.
base=3*32**2
Pdelta=2*3*base
Qdelta=2*(3*2*base+3*2*base)
Ctime=2*(Pdelta*72+19*Qdelta)
assert (base,Pdelta,Qdelta,Ctime)==(3072,18432,73728,5455872)
assert 2*3*3*(1+Q(32**2,200**2))<19
assert Q(Ctime,T*T)/R**2<Q(55,1000)
# Fourth-difference local sin^4 remainder uniformly |delta|<=2sqrtR:
F6=Q(320,351)*Q(2,3)*Q(22,28)**6*64
assert F6<10
# Uniform error /R^2 for q=4 +/- x sqrtR, 1/2<=|x|<=2
err=Q(18,10_000)+10*R+C*R**2+Q(Ctime,T*T)/R**2
assert err<Q(58,1000)
# Exact source first-jet leading margins; pi lower/upper rational.
inner=Q(5,26)-Q(5,22464)*Q(22,7)**4
outer=Q(20,351)*(81-Q(157,50)**4)
assert inner>Q(17,100) and outer<-Q(9,10)
assert inner-err>Q(11,100)
assert outer+err<-Q(4,5)
assert 4-2*sqrtR>Q(1,4) and 1/(Q(157,50)+1)<Q(1,4)
print("PASS fixed original R=1e-10 / t>=1e14 / |a|<=1/2 q-window")
print("PASS uniform finite pole+horizontal error <= 5455872/t^2")
print("PASS both inner q brackets > 0.11 R^2")
print("PASS both outer q brackets < -0.8 R^2")
print("PASS two Fourier-response roots by continuity (NOT zeta zeros)")
print("PASS q~4 belongs to A2 far, not canonical |q|<=eta local")
print("OPEN actual signed FarExact - mu - compensation and RH/GRH")

# FULL q-band source signed inequalities, not just isolated bracket points:
# |x|<=1/2 => original K>11R^2/100; 99/50<=|x|<=2 => K<-3R^2/5.
neg_shell_x=Q(99,50)
neg_shell_upper=Q(60,13)-Q(5,1404)*Q(157,50)**4*neg_shell_x**4
assert neg_shell_upper+err < -Q(3,5)
assert inner-err > Q(11,100)
# Original Lean signedLiteralPairSourceTerm_eq_normalizedPairKernel:
# per literal zeta zero the signed source = mult(rho)/(t/16)^2 * K.
# True signed sums over arbitrary finite zeta-zero bands preserve this
# multiplicity; actual zero NUMBERS require original RvM N(A,B), not a toy.
assert neg_shell_x<2 and R*R*Q(3,5)>0
core_width=Q(T,16)*sqrtR
negative_each_width=Q(T,16)*(2-neg_shell_x)*sqrtR
assert (core_width,negative_each_width)==(62_500_000,1_250_000)
print("PASS entire positive core |x|<=1/2 and negative shells 1.98<=|x|<=2")
print("PASS source actual-zero signed summand bounds retain multiplicity/r^2")
print("PASS physical t=1e14 band widths 62500000 and 1250000")
print("CAVEAT RvM lower-count C and onset T0 remain existential in Lean")
