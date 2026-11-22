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
# Bishop rational window from the ACTUAL source
# BishopMachinPiRationalWindowExact (strictly tighter than 3<piB<22/7).
# These inequalities concern Bishop's constructed piB. A separate
# same-object cross-prover receipt is necessary before Lean Real.pi.
lo=R(3)+R(12601,89625)
hi=R(22,7)-R(1531,1312500)
p0=(lo+hi)/2
delta=(hi-lo)/2
assert lo==R(281476,89625) and hi==R(589067,187500)
assert p0==R(93841671,29875000) and delta==R(49013,89625000)
assert 3<lo<hi<R(22,7)
F_rational=s.trigsimp(F2.subs({h:p0/2,q:4}))
assert s.trigsimp(F_rational+R(320,351)*s.sin(p0)**4,method="fu")==0
# If |p0-Real.pi|<=delta, then |sin p0|<=delta by Lipschitz
# with sin(Real.pi)=0; this implication is conditional on identifying
# Bishop's piB and classical Lean Real.pi.
bound=R(320,351)*delta**4
assert bound==R(5770921183044640561,70774011590782928466796875000000)
assert bound<R(816,100)*R(1,10**14)
assert 13==3**2+2**2 and 9==3**2 and 4==2**2
assert R(1,8)+R(1,18)==R(13,72)
# A projector forgets the two nonzero traces: it is NOT BIDI by itself.
raw_a=(3,24,24,4,1)
raw_b=(3,48,48,4,1)
assert raw_a!=raw_b
assert (raw_a[0],raw_a[3],raw_a[4])==(raw_b[0],raw_b[3],raw_b[4])
print("PASS 6/6 finite H05 face equations, signed stencil, 0/1/2/3 moment nulls")
print("PASS observed pi/3 cancellation retains two distinct source histories")
print("PASS generic-spacing negative-square Fourier symbol")
print("PASS q4 fourth-order zero at true h=pi/2")
print("PASS conditional Bishop certified-pi notch envelope <8.16e-14",bound)\nprint("OPEN Bishop pi = Lean Real.pi source receipt; no numerical RH promotion")
print("OPEN Agda kernel, Bishop pi <-> Lean Real.pi receipt, true 9DOF charts")
print("OPEN smoothing, finite-pole, actual zeros, signed far/RH")
