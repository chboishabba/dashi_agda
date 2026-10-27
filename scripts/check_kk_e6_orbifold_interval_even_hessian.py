#!/usr/bin/env python3
"""All-18-even real Higgs functional spectral test ON A NONCONSTANT interval.

Original repo E6 V6 and E32/E33: PR #1106. Physical S1/Z2 parity,
E21 boundary Higgs: KK PR #1241.
Classical source E = int_0^1 [1/2 |Phi'|²+1/2|Chi'|² + V6]
   + W(Chi(0)) + W(Chi(1)), where fixed-plane W =
  -mu2/2 Tr(P2 Chi P2 Chi†)+lambda/2 (Tr...)².
This is the explicitly NORMALIZED DIMENSIONLESS scalar comparison
action, NOT the physical b0=1e-24m 5D source. No fermions, Yang-Mills
gauge ghosts, radion, gravity, quantum CS or global anomaly here.

Solve correct nonconstant three-amplitude bulk+Robin boundary-value
problem and then evaluate the FULL orbifold-even 18-real fluctuation
second variation including the scalar interval kinetic Laplacian and
source-fixed endpoint Hessians. Piecewise linear FEM at N=32 and64:
seven near-zero gauge directions converge as h², remaining low 11
modes positive with eighth eigenvalue >2.0 in chosen units.
This is a COMPUTATIONAL local spectrum receipt, not a rigorous
continuum proof, and does not check parity-odd KK/UV quantum sectors.
"""
import numpy as np
import torch
from scipy.integrate import solve_bvp
from scipy.sparse import lil_matrix, diags
from scipy.sparse.linalg import eigsh

torch.set_default_dtype(torch.float64)
P=(-1,-1,1)
mu2=3.00090774
quartic=4.0

def rhs(x,u):
    a,b,t,da,db,dt=u
    return np.vstack((da,db,dt,4*a**3+2*a*t*t-4*a,
                      4*b**3+8*b*t*t-4*b,
                      2*a*a*t+8*b*b*t+4*t**3-4*t))

def bc(u0,u1):
    return np.array((u0[3],u0[4],
       u0[5]+mu2*u0[2]-2*quartic*u0[2]**3,
       u1[3],u1[4],
       u1[5]-mu2*u1[2]+2*quartic*u1[2]**3))

x=np.linspace(0,1,81)
t=.33*np.cosh(2*(x-.5))/np.cosh(1)
init=np.vstack((np.sqrt(1-t*t/2),np.sqrt(1-2*t*t),t,
  np.zeros_like(t),np.zeros_like(t),
  .66*np.sinh(2*(x-.5))/np.cosh(1)))
sol=solve_bvp(rhs,bc,x,init,tol=1e-8,max_nodes=5000)
assert sol.status==0 and np.max(np.abs(bc(sol.sol(0),sol.sol(1))))<1e-8
projector=torch.diag(torch.tensor([1.,1.,0.],dtype=torch.complex128))

def as_complex(z):
    ph=torch.complex(z[:9].reshape(3,3),z[9:18].reshape(3,3))
    ch=torch.complex(z[18:27].reshape(3,3),z[27:36].reshape(3,3))
    return ph,ch

def sourceV6(z):
    phi,chi=as_complex(z)
    u=phi.conj().T@phi
    w=chi.conj().T@chi
    nphi=torch.trace(u).real
    nchi=torch.trace(w).real
    return ((nphi-1)**2+(nchi-1)**2
       +nphi*nphi-torch.trace(u@u).real
       +nchi*nchi-torch.trace(w@w).real
       +torch.trace(u@w).real+nphi*nchi
       -torch.trace((phi@phi.conj().T)@(chi@chi.conj().T)).real)

def boundaryW(z):
    _,chi=as_complex(z)
    q=projector@chi@projector
    r=torch.trace(q@q.conj().T).real
    return -mu2*r/2+quartic*r*r/2

phi_even=[i*3+j for i in range(3) for j in range(3)
          if -P[i]*P[j]==1]
chi_even=[i*3+j for i in range(3) for j in range(3)
          if P[i]*P[j]==1]
even=phi_even+[9+i for i in phi_even]+\
     [18+i for i in chi_even]+[27+i for i in chi_even]
assert len(even)==18

def scalar_hessians(a,b,t):
    z=torch.zeros(36)
    z[7]=a
    z[18+8]=b
    z[18+3]=t
    hv=torch.autograd.functional.hessian(sourceV6,z).detach().numpy()
    hw=torch.autograd.functional.hessian(boundaryW,z).detach().numpy()
    return hv[np.ix_(even,even)],hw[np.ix_(even,even)]

def interval_low_modes(N):
    nodes=np.linspace(0,1,N+1)
    step=1/N
    size=18*(N+1)
    K=lil_matrix((size,size),dtype=float)
    Mdiag=np.zeros(size)
    for i,y in enumerate(nodes):
        a,b,t=sol.sol(y)[:3]
        h_bulk,h_boundary=scalar_hessians(a,b,t)
        weight=.5 if i in (0,N) else 1.
        block=slice(18*i,18*(i+1))
        K[block,block]+=step*weight*h_bulk
        Mdiag[block]=step*weight
        if i in (0,N):
            K[block,block]+=h_boundary
    for i in range(N):
        for k in range(18):
            a=18*i+k
            b=18*(i+1)+k
            K[a,a]+=1/step
            K[b,b]+=1/step
            K[a,b]-=1/step
            K[b,a]-=1/step
    assert np.min(Mdiag)>0
    W=diags(1/np.sqrt(Mdiag))
    operator=(W@K.tocsr()@W).tocsr()
    return np.sort(eigsh(operator,k=18,which="SA",
                         tol=1e-7,maxiter=50000,
                         return_eigenvectors=False))

coarse=interval_low_modes(32)
fine=interval_low_modes(64)
assert np.all(coarse[:7]>=-1e-6)
assert np.all(fine[:7]>=-1e-6)
assert max(fine[:7])<.0011
assert fine[7]>2.0 and coarse[7]>2.0
assert max(fine[:7])<max(coarse[:7])*.30
assert np.all(fine[7:]>1.9)
print("32-element interval smallest 18:",coarse)
print("64-element interval smallest 18:",fine)
print("seven gauge-orbit directions approach zero ~quadratic mesh refinement")
print("first nonzero even Higgs spectral eigenvalue:",fine[7])
print("PASS two-grid local 18-real parity-even interval quadratic-form test, conditional comparison action")
print("OPEN continuum interval operator proof, physical E6 source normalisation, parity-odd tower, anomaly and metric/quantum stress")
