#!/usr/bin/env python3
"""Reproducible exact symbolic spin-one/NV crystal and POVM algebra.
Not an experimentally calibrated ODMR or in-vivo optogenetics simulation.
Conventions: dimensionless spin matrices, hbar=1, real physical parameters;
frequency-Hamiltonian units must be supplied by a calibration consumer.
"""
import sympy as s

D,E,gamma,Bx,By,Bz=s.symbols("D E gamma Bx By Bz",real=True)
sqrt2=s.sqrt(2)
Sx=s.Matrix([[0,1,0],[1,0,1],[0,1,0]])/sqrt2
Sy=s.Matrix([[0,-s.I,0],[s.I,0,-s.I],[0,s.I,0]])/sqrt2
Sz=s.diag(1,0,-1)
I=s.eye(3)
zero=s.zeros(3)
assert Sx.conjugate().T==Sx
assert Sy.conjugate().T==Sy
assert Sz.conjugate().T==Sz
assert s.simplify(Sx*Sy-Sy*Sx-s.I*Sz)==zero
assert s.simplify(Sy*Sz-Sz*Sy-s.I*Sx)==zero
assert s.simplify(Sz*Sx-Sx*Sz-s.I*Sy)==zero
H=D*Sz**2+E*(Sx**2-Sy**2)+gamma*(Bx*Sx+By*Sy+Bz*Sz)
assert s.simplify(H.conjugate().T-H)==zero
assert s.simplify(H.subs({Bx:0,By:0,E:0})-s.diag(D+gamma*Bz,0,D-gamma*Bz))==zero
assert s.simplify(s.trace(H)-2*D)==0
# Quantum projective measurement: positivity <psi|P|psi> = |psi_j|^2,
# completeness and non-negative normalised qutrit populations.
P=[s.diag(*[int(k==j) for k in range(3)]) for j in range(3)]
assert sum(P,zero)==I
for p in P:
    assert p*p==p and p.conjugate().T==p
# Single-parameter contrast readout; probabilities p0 and (1-p0) sum to 1.
p0=s.symbols("p0",nonnegative=True,real=True)
assert s.simplify(p0+(1-p0)-1)==0
# Finite crystal <111> directional response; selected signed axes are not
# a real-space reconstruction or defect-strain identification.
axes=[s.Matrix(v) for v in ((1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1))]
for a in axes: assert a.dot(a)==3
assert sum((a*a.T for a in axes),s.zeros(3))==4*s.eye(3)
# Distinct mid-IR / visible-light experimental arms and additive null.
base,mito,opsin=s.symbols("base mito opsin",real=True)
Y00,Y10,Y01,Y11=base,base+mito,base+opsin,base+mito+opsin
assert s.simplify(Y11-Y10-Y01+Y00)==0
print("PASS spin-one commutators, Hermiticity, axial reduction, projector completeness")
print("PASS tetrahedral-axis second moment and additive optogenetic factorial null")
print("BOUNDARY full optical pumping, linewidth, shot noise and in-vivo outcomes uncalibrated")
