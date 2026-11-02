#!/usr/bin/env python3
"""Orbifold E6 first-Tits 2-VEV + electroweak boundary Higgs full Hessian.

Source: #1106's ACTUAL six-invariant two-bifundamental V6, E32/E33;
orbifold parity #1241: P_L=P_R=diag(-,-,+), intrinsic Phi ODD,
Chi EVEN. One allowed boundary coupling -mu2 Tr(P2 Chi P2 Chi†)
+lambda [Tr(P2 Chi P2 Chi†)]², invariant under the EVEN orbifold
gauge group (NOT whole SU3LxSU3R bulk).
For t=0.0246,lambda=4,mu2=3+1.5t²:
  Phi=a E32,a²=1-t²/2;
  Chi=b E33+t E21,b²=1-2t²;
  exact restricted-stationary solution of cubic E32,E33,E21
  and numerically full 36-real gradient=0.
IMPORTANT CORRECTION (2026-10-25): This evaluates an INTEGRATED
CONSTANT-ZERO-MODE potential and its homogeneous Hessian, NOT the
complete 5D interval Euler-Lagrange equations. At t=.0246 the
separate BULK t-force is ~+.14740647 and boundary source force cancels
it only AFTER zero-mode integration. A constant field therefore FAILS
the five-dimensional bulk E-L and Robin boundary equations. New actual
comparison model: check_kk_e6_orbifold_interval_higgs_bvp.py.
Hessian in 36 REAL bulk coordinates has 2 negative directions,
BOTH ORBIFOLD-ODD: these are not 4D constant zero modes.
Physical zero-mode scalar sector is 18 real EVEN coordinates,
with 7 gauge-orbit zeros and 11 strictly POSITIVE curvatures.
This is a local TREE-LEVEL, dimensionless Hessian receipt ONLY.
Odd KK tower and boundary conditions, UV anomaly, actual SM masses,
quantum renormalized interval Casimir/metric stress remain OPEN.

Requires numpy, torch (CPU autograd). The representation/potential and
orbifold anomaly sources retain their original literature attribution.
"""
import numpy as np
import torch
T=torch
T.set_default_dtype(T.float64)
t=0.0246
quartic=4.0
mu2=3+(2*quartic-6.5)*t*t
a=(1-t*t/2)**.5
b=(1-2*t*t)**.5
x=T.zeros(36)
x[2*3+1]=a                 # Re Phi E32
x[18+2*3+2]=b              # Re Chi E33
x[18+1*3+0]=t              # Re Chi E21
p=T.diag(T.tensor([1.,1.,0.],dtype=T.complex128))
def energy(v):
    phi=T.complex(v[:9].reshape(3,3),v[9:18].reshape(3,3))
    chi=T.complex(v[18:27].reshape(3,3),v[27:36].reshape(3,3))
    u=phi.conj().T@phi
    w=chi.conj().T@chi
    nphi=T.real(T.trace(u))
    nchi=T.real(T.trace(w))
    original=((nphi-1)**2+(nchi-1)**2
      +nphi*nphi-T.real(T.trace(u@u))
      +nchi*nchi-T.real(T.trace(w@w))
      +T.real(T.trace(u@w))
      +nphi*nchi
      -T.real(T.trace((phi@phi.conj().T)@(chi@chi.conj().T))))
    projected=p@chi@p
    even_norm=T.real(T.trace(projected@projected.conj().T))
    return original-mu2*even_norm+quartic*even_norm*even_norm

v=x.clone().requires_grad_()
grad=T.autograd.grad(energy(v),v)[0].detach().numpy()
H=T.autograd.functional.hessian(energy,v).detach().numpy()
assert np.max(np.abs(grad))<1e-10
assert np.max(np.abs(H-H.T))<1e-10
P=(-1,-1,1)
phi_even=[i*3+j for i in range(3) for j in range(3)
          if -P[i]*P[j]==1]
chi_even=[i*3+j for i in range(3) for j in range(3)
          if P[i]*P[j]==1]
even=phi_even+[9+i for i in phi_even]+[18+i for i in chi_even]+[27+i for i in chi_even]
odd=[j for j in range(36) if j not in even]
assert len(even)==18 and len(odd)==18
assert np.max(np.abs(H[np.ix_(even,odd)]))<1e-10
eigens=np.linalg.eigvalsh(H[np.ix_(even,even)])
odd_eigens=np.linalg.eigvalsh(H[np.ix_(odd,odd)])
assert sum(eigens < -1e-8)==0
assert sum(abs(eigens)<=1e-8)==7
assert sum(eigens>1e-8)==11
assert sum(odd_eigens < -1e-8)==2
assert min(z for z in eigens if z>1e-8)>0.0036
# 8 orbifold-even LR gauge generators -> one unbroken photon,
# so seven even scalar Goldstones are exactly as expected.
print("mu2",mu2,"a",a,"b",b,"t",t)
print("full_gradient_max",np.max(np.abs(grad)))
print("even_modes",len(even),"even_Hessian_(negative,zero,positive)",
      (sum(eigens<-1e-8),sum(abs(eigens)<=1e-8),sum(eigens>1e-8)))
print("smallest_even_positive_curvature",min(z for z in eigens if z>1e-8))
print("odd_modes",len(odd),"odd_Hessian_negative",sum(odd_eigens<-1e-8),
      "odd_minimum",min(odd_eigens))
bulk_force=t*(6-13*t*t)
boundary_force=-2*mu2*t+4*quartic*t**3
assert abs(bulk_force)>.14 and abs(bulk_force+boundary_force)<1e-12
print("NONZERO BULK E-L t-force at old constant profile:",bulk_force)
print("ZERO-MODE source cancellation only; NOT a 5D Robin interval vacuum")
print("PASS stationary HOMOGENEOUS TRUNCATION and parity-even 18-real zero-mode Hessian")
print("OPEN odd interval KK tower positivity (odd modes have no constant zero mode); no all-field/quantum/global vacuum proof")
