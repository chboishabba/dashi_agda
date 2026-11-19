#!/usr/bin/env python3
"""Backward electroweak/flavour acceptance, NOT a derived CY vacuum.
Classical Higgs mechanism, MSSM tree quartic, CKM/PMNS and seesaw.
Original DASHI CarrierHiggsMassReceipt, CKM physical mass diagnostics,
NeutrinoSameLeptonMassOperatorRationalExact, SignedZeroTernaryOrientationExact,
ArgumentResponseNonGeometricOppositeBidiExact, E6 #1106/#1241.
New comparison and exact conditional rank/symmetry constraints.
"""
import numpy as np
import sympy as s
from math import pi,sqrt
v=246.22
mh=125.065 # CMS HIG-26-010, uncertainty .088 GeV
mz=91.1876 # benchmark input, not prediction
mw=80.3692 # illustrative EW input
lam=mh**2/(2*v*v)
phi=(1+sqrt(5))/2
old=phi*v/pi
print("CMS tree-equivalent lambda",lam,"old estimate",old,
      "mass difference",old-mh,"measurement-only pull",(old-mh)/.088)
print("MSSM tree upper bound",mz,"minimum mass-square correction",mh**2-mz**2)
g=2*mw/v; gp=sqrt((2*mz/v)**2-g*g)
print("tree calibrated g,gprime",g,gp)
# Exact gauge mass matrix: no photon mass, one neutral massive state.
a,b,h=s.symbols("g gp v",positive=True)
N=h*h/4*s.Matrix([[a*a,-a*b],[-a*b,b*b]])
assert N*s.Matrix([b,a])==s.zeros(2,1)
assert N*s.Matrix([a,-b])==s.expand(h*h*(a*a+b*b)/4)*s.Matrix([a,-b]) or all(s.simplify(z)==0 for z in N*s.Matrix([a,-b])-h*h*(a*a+b*b)/4*s.Matrix([a,-b]))
# Backward tree EFT benchmark. Inputs are illustrative masses; quark
# scale/scheme differences mean these are NOT one running Yukawa table.
masses={"u":.00216,"c":1.27,"t":172.5,"d":.00467,"s":.0934,"b":4.18,
        "e":.000510999,"mu":.105658,"tau":1.77686}
print("illustrative Yukawa targets",{k:sqrt(2)*m/v for k,m in masses.items()})
# Reproduce old source texture (no dependent checkout required).
a1=.041240; delta=np.angle((1+2j*sqrt(7))/(5+2j))
Y=np.array([[a1*2*pi,a1*pi*sqrt(3),a1**3*24*pi/sqrt(6)*np.exp(1j*delta)],
 [0,a1**2*4*pi/3,a1**2*14/sqrt(24)*8*pi/3],[0,0,a1**3*8*pi/3]])
print("old carrier down masses",np.sort(np.linalg.svd(Y*v/sqrt(2),compute_uv=False)))
# Physical left mixing is UuL^dagger UdL, not right eigenvectors alone.
# If both physical Hermitian mass operators commute with same simple C3,
# both diagonalize in its character basis; CKM magnitudes permutation.
C=s.Matrix([[0,0,1],[1,0,0],[0,1,0]])
p,q,r,u,w,z=s.symbols("p q r u w z")
A=p*s.eye(3)+q*C+r*C**2
B=u*s.eye(3)+w*C+z*C**2
assert A*B==B*A
# Combined geometry-gauge invariance does not impose a family C3 on
# the surviving multiplicity space; therefore this is a conditional warning.
# Binary support of a signed axis is separate from its orientation.
for plus,minus in [(1,0),(0,1),(1,1),(0,0)]:
    occupancy=plus+minus; orientation=plus-minus
    assert ((occupancy+orientation)//2,(occupancy-orientation)//2)==(plus,minus)
# 10 paired +3 single axes: orientation sum of single support is not
# a fermion index without a bundle map. Signed opposite is not logical negation.
print("PASS exact electroweak neutral mass matrix, common-C3 flavour obstruction, binary occupancy/orientation reconstruction")
print("OPEN CY matter metrics, F/D vacuum, soft SUSY parameters, RG, mass and CMS differential predictions")
