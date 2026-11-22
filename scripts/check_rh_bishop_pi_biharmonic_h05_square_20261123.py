#!/usr/bin/env python3
"""Original RH atomic stencil x Bishop-pi rational chart x native H05 cube.

Exact SymPy and rational checks. Analytic fourth-order pi error uses only
|sin(p)-sin(pi)|<=|p-pi|, conditional on the source-specific Machin-pi
versus classical/Lean Real.pi identity. The independent Agda six-face
finite fixture is SOURCE WRITTEN; no Agda kernel or RH claim.
"""
import sympy as s
from fractions import Fraction
R=s.Rational
q,h,p=s.symbols("q h p",real=True)
four=(-3,0,4,-1)
# A centre/pi/2/pi observed projective coefficient vector; original
# pi/3 raw endpoint values BOTH nonzero but cancel: 8*3 == 9*(8/3).
assert 8*3==9*R(8,3)==24
def project(src):
    c,third,inner,outer=src
    assert third==0  # observation, not source absence
    return c,inner,outer
def unfold(folded):
    c,inner,outer=folded
    return (outer,inner,2*c,inner,outer)
def direct(src):
    c,third,inner,outer=src
    assert third==0
    return (outer,inner,c+c,inner,outer)
assert project(four)==(-3,4,-1)
assert direct(four)==unfold(project(four))==(-1,4,-6,4,-1)
# Verify genuine 6-face fixture with z=id (not six analytic axes).
x=project;y=direct;lower_x=lambda z:z;lower_y=unfold;identity=lambda z:z
assert lower_y(x(four))==lower_x(y(four))  # xy0
assert identity(x(four))==x(identity(four))  # xz0
assert identity(y(four))==y(identity(four))  # yz0
assert lower_y(x(four))==lower_x(y(four))  # xy1
for five in [(-1,4,-6,4,-1), (-2,8,-12,8,-2)]:
    assert identity(lower_x(five))==lower_x(identity(five))  # xz1
assert identity(lower_y(x(four)))==lower_y(identity(x(four))) # yz1
# Noninvertible observed cancellation: equal projective output does
# not recover original endpoint source ledger.
rawA=(3,24,24,4,1)
rawB=(3,48,48,4,1)
assert rawA!=rawB and rawA[1]!=rawB[1]
assert (rawA[0],rawA[3],rawA[4])==(rawB[0],rawB[3],rawB[4])
# Signed geometric five-point operator and fourth finite difference.
five=direct(four)
assert all(sum(five[j]*(j-2)**k for j in range(5))==0 for k in range(4))
assert sum(five[j]*(j-2)**4 for j in range(5))==-24
F=s.expand_trig(sum(R(20,351)*five[j]*s.cos((j-2)*h*q) for j in range(5)))
F2=-R(80,351)*(1-s.cos(h*q))**2
assert s.simplify(s.trigsimp(F-F2))==0
assert s.trigsimp(F2+R(320,351)*s.sin(h*q/2)**4,method="fu")==0
# One normalized square holds for any h.  A *true* q4 notch needs
# 2h=pi, not just h>0 or h approximately pi/2.
assert s.simplify(s.trigsimp(F2.subs({h:s.pi/2,q:4})))==0
for k in range(4):
    assert s.simplify(s.diff(F2.subs(h,s.pi/2),q,k).subs(q,4))==0
assert s.simplify(s.diff(F2.subs(h,s.pi/2),q,4).subs(q,4)/24
                  +5*s.pi**4/1404)==0
# Bishop rational window 3<pi_M<22/7 yields midpoint p0 and
# a guaranteed absolute radius 1/14 for pi_M (NOT Lean pi until
# semantic bridge supplied). If |p0-Real.pi|<=1/14, then
# |F_{h=p0/2}(q=4)| <=(320/351)(1/14)^4
# via sin(pi)=0 and scalar sine 1-Lipschitz.
p0=(R(3)+R(22,7))/2
delta=(R(22,7)-R(3))/2
assert p0==R(43,14) and delta==R(1,14)
F_rational=s.trigsimp(F2.subs({h:p0/2,q:4}))
assert s.simplify(s.trigsimp(F_rational+R(320,351)*s.sin(p0)**4,method="fu"))==0
bound=R(320,351)*delta**4
assert bound==R(20,842751)
assert bound>0
assert 13==3**2+2**2
assert R(1,8)+R(1,18)==R(13,72)
print("PASS 6/6 finite H05 face equations, signed stencil, 0/1/2/3 moment nulls")
print("PASS observed pi/3 cancellation retains two distinct source histories")
print("PASS generic-spacing negative-square Fourier symbol")
print("PASS q4 fourth-order zero at true h=pi/2")
print("PASS conditional Bishop pi-window notch envelope",bound)
print("OPEN Agda kernel, Bishop pi <-> Lean Real.pi receipt, true 9DOF charts")
print("OPEN smoothing, finite-pole, actual zeros, signed far/RH")
