#!/usr/bin/env python3
"""Exact selected-W SU3 trace -> spectral cubic -> sharper marked child bound.

Original roots: classical SU3 spectral/characteristic/Newton identities;
Hatcher, Algebraic Topology Ex 2B.2 marked wild horn free-group
commutators; Goto 1949 compact semisimple commutator surjectivity.
Existing DASHI neutrino Agda #1247 owns the exact selected SU3 W and
trace; Agda #1249 / Lean #84 own earlier direct-arc bound.
This script computes an improved consequence; it does not construct
source-marked geometrical loops, field strengths or experiments.
"""
from fractions import Fraction as Q
from math import pi

D = 181846007130841
# Exact tr W=(a-b*zeta)/D, zeta=-1/2+i*sqrt(3)/2.
a = Q(176093404722400, D)
b = Q(19836986431118, D)
t = a + b/2              # Re tr(W)
u_sq = Q(3,4)*b*b         # Im tr(W)^2

# For W in SU3, X=(W-I)^*(W-I)=2I-W-W^*, xi>=0.
# det W=1 implies tr W^2=(tr W)^2-2 conjugate(tr W).
# Hence characteristic polynomial of X:
# p(x)=x^3-2(3-t)x^2+((3-t)^2+u^2)x-4u^2.
e1 = 2*(3-t)
e2 = (3-t)**2+u_sq
e3 = 4*u_sq
p = lambda x: x**3-e1*x*x+e2*x-e3

q = Q(517,250)  # 2.068, exact spectral threshold
assert p(q) == -Q(78609668791519322720866577865447,
                    516687036084841809701458863765625000)
assert p(q) < 0
# All eigenvalues of X are real nonnegative; p(q)<0 means one xi>q.
print("PASS exact source-W spectral ||W-I||_op^2 > 517/250")
print("p(517/250) =", p(q))

# Direct sharp cap for a child B: d([A,B])^2 <=4*s^2-s^4
# if 0<=d(B)<=s<=sqrt(2). Valid for EITHER child by symmetry.
arc_sq = lambda s: 4*s*s-s**4
child = Q(781,1000)
assert arc_sq(child)<q
assert q-arc_sq(child)==Q(208421521,10**12)
print("PASS selected W flat commutator requires BOTH child gaps > 781/1000")

# Curved source: actual based parent-to-commutator Wilson defect eta.
# For one TRUE child gap <=3/4:
#   direct commutator gap <1391/1000 (by squared cap)
#   root gap >1437/1000 (by new spectral cubic)
#   eta <=23/500=46/1000 => contradiction, exact rational.
s, upper, lower, eta = Q(3,4),Q(1391,1000),Q(1437,1000),Q(23,500)
assert arc_sq(s)==Q(495,256)
assert arc_sq(s)<upper**2
assert q>lower**2
assert upper+eta==lower
print("PASS source-conditional curved one-stage: child <=3/4, eta <=23/500")

# Negative controls: abstract root/curvature cannot source a geometric
# loop, and d(child)=4/5 does NOT force a contradiction.
assert arc_sq(Q(4,5))>q
print("PASS fail-closed child=4/5 and absent based source Hatcher homotopy")

# Independently evaluate the selected SU3 fixture already in neutrino
# PR #1247 (illustrative, NOT a sourced physical lepton prediction).
try:
    import numpy as np
    z=np.exp(2j*pi/3)
    s12,c12=161/289,240/289
    s13,c13=240/1609,1591/1609
    s23,c23=20/29,21/29
    U=np.array([
        [c12*c13,s12*c13,s13*np.conj(z)],
        [-s12*c23-c12*s23*s13*z,c12*c23-s12*s23*s13*z,s23*c13],
        [s12*s23-c12*c23*s13*z,-c12*s23-s12*c23*s13*z,c23*c13]
    ],dtype=complex)
    W=np.diag([1,z,z*z])@(2*np.outer(U[:,0],np.conj(U[:,0]))-np.eye(3))
    X=(W-np.eye(3)).conj().T@(W-np.eye(3))
    spectrum=np.linalg.eigvalsh(X)
    assert np.linalg.norm(W@W.conj().T-np.eye(3),ord=2)<1e-10
    assert abs(np.linalg.det(W)-1)<1e-10
    assert abs(np.trace(W).real-float(t))<1e-10
    assert abs(np.trace(W).imag**2-float(u_sq))<1e-10
    assert all(abs(float(p(Q.from_float(float(xi)))) )<1e-8 for xi in spectrum)
    assert spectrum.max()>float(q)
    print("PASS independent original 3x3 SU3 fixture, X eigenvalues",spectrum)
except ImportError:
    print("SKIP optional numpy original-fixture spectrum")

print("OPEN actual Hatcher marked meridians, arclength, based Stokes curvature")


# EXACT isolating intervals for ALL THREE squared SU3 eigenvalue gaps.
# Each polynomial endpoint pair has opposite strict rational signs.
# Intervals are pairwise disjoint, so IVT and degree=3 show precisely
# one real eigenvalue in each interval. This closes the finite scalar
# spectrum certificate; it is NOT a new geometric or physical spectrum.
intervals=[
    (Q(919,100000),Q(920,100000)),
    (Q(187659,100000),Q(187660,100000)),
    (Q(206838,100000),Q(206839,100000))
]
assert all(p(lo)*p(hi)<0 for lo,hi in intervals)
assert all(intervals[i][1]<intervals[i+1][0]
           for i in range(len(intervals)-1))
print("PASS exact rational complete 3-eigenvalue squared-gap root isolation")
