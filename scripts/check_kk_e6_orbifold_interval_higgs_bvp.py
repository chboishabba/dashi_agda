#!/usr/bin/env python3
"""Correct the previous zero-mode-only EW Hessian with a genuine interval BVP.

DONOR and original authorship:
  #1106 first-Tits E6-derived gauged SU3^3 E32/E33 V6
  #1241 S1/Z2 parity, Chi E21 fixed-plane gauge-invariant term.
  Boundary scalar variational problems, Robin conditions and brane
  Higgs spectral problems are established physics/mathematics;
  Leng/Moreau/Nortier PRD 103 (2021) 075010 and
  Barceló/Mitra/Moreau EPJC 75 (2015) 527 stress BC regularization.

This new script tests ONE declared *dimensionless* scalar interval action:
  E = int_0^1 [ 1/2(a'^2+b'^2+t'^2) + V6(a,b,t) ] dy
      + W(t(0)) + W(t(1)),
  W = -mu2*t^2/2 + lambda*t^4/2.
This choice of normalized interval length and canonical kinetic metric is a
NEW comparison model, not the earlier b0=1e-24m physical KK action.
Field profiles: Phi=a(y) E32, Chi=b(y) E33 + t(y) E21.
E32/E33 are the old first-Tits source; E21 is orbifold-even.

The old constant-profile 36-real Hessian tested only the INTEGRATED
zero-mode potential. At its reported a,b,t, the interior bulk equation
has nonzero t force, and cannot solve the actual 5D interval equations.
A full *nonconstant* BVP profile is constructed here, and tested against
all 36 bulk scalar Euler-Lagrange equations and all 16 gauge-orbit current
components (source A_y=0 is consistent in this restricted ansatz).

Still OPEN: complete all-18-scalar functional Hessian and interval KK
spectrum, boundary/radion quantum path, 5D global anomaly/Green-Schwarz
and chiral exotic masses, actual gauge/Higgs kinetic parameter matching.
"""
import numpy as np
from scipy.integrate import solve_bvp, simpson
from scipy.linalg import eigh
import sympy as sp

mu2 = 3.00090774
lam = 4.0
L = 1.0
t_previous = .0246
a_prev = np.sqrt(1 - t_previous*t_previous/2)
b_prev = np.sqrt(1 - 2*t_previous*t_previous)
bulk_t_old = t_previous*(6-13*t_previous*t_previous)
bdry_t_old = (-2*mu2*t_previous+4*lam*t_previous**3)
assert abs(bulk_t_old) > .14 and abs(bulk_t_old+bdry_t_old) < 1e-12

def V6(a,b,t):
    return (a**4+a*a*t*t-2*a*a+
            b**4+4*b*b*t*t-2*b*b+t**4-2*t*t+2)

def rhs(y,u):
    a,b,t,da,db,dt=u
    return np.vstack((da,db,dt,
        4*a**3+2*a*t*t-4*a,
        4*b**3+8*b*t*t-4*b,
        2*a*a*t+8*b*b*t+4*t**3-4*t))

def boundary(left,right):
    a,b,t,da,db,dt=left
    A,B,T,dA,dB,dT=right
    return np.array([da,db,dt+mu2*t-2*lam*t**3,
                     dA,dB,dT-mu2*T+2*lam*T**3])

x=np.linspace(0,L,101)
init_t=.33*np.cosh(2*(x-L/2))/np.cosh(L)
init_dt=.33*2*np.sinh(2*(x-L/2))/np.cosh(L)
guess=np.vstack((np.sqrt(1-init_t**2/2),
                  np.sqrt(1-2*init_t**2),
                  init_t,np.zeros_like(x),np.zeros_like(x),init_dt))
sol=solve_bvp(rhs,boundary,x,guess,tol=2e-9,max_nodes=12000)
assert sol.status==0,sol.message
z=sol.sol(np.linspace(0,L,401))
assert max(abs(boundary(z[:,0],z[:,-1])))<1e-8
assert np.max(abs(sol.sol(x,1)-rhs(x,sol.sol(x))))<2e-7
assert .38 < z[2,0] < .40 and .22 < z[2,200] < .24
assert max(abs(z[3:].flatten()))>.65  # definitely NON-constant
assert max(abs(z[0]-a_prev))>.01  # full VEV relaxation differs
energy=simpson(
    .5*np.sum(z[3:]**2,axis=0)+V6(*z[:3]),
    x=np.linspace(0,L,401))
energy+= (-mu2/2*(z[2,0]**2+z[2,-1]**2)
         +lam/2*(z[2,0]**4+z[2,-1]**4))
assert energy < -.06  # versus zero-field EW branch E=0

# The restricted 3-field ansatz is a consistent scalar-sector
# submanifold for this SOURCE V6: exact sympy first variations
# outside its E32/E33/E21 coordinates are zero (independent tested
# here with the literal complex 3x3 V6 definition at selected sites).
import torch as T
T.set_default_dtype(T.float64)
def source_gradient36(a,b,t):
    v=T.zeros(36);v[7]=a;v[18+8]=b;v[18+3]=t
    v.requires_grad_()
    phi=T.complex(v[:9].reshape(3,3),v[9:18].reshape(3,3))
    chi=T.complex(v[18:27].reshape(3,3),v[27:36].reshape(3,3))
    u=phi.conj().T@phi;w=chi.conj().T@chi
    nphi=T.trace(u).real;nchi=T.trace(w).real
    original=((nphi-1)**2+(nchi-1)**2+nphi*nphi-
      T.trace(u@u).real+nchi*nchi-T.trace(w@w).real+
      T.trace(u@w).real+nphi*nchi-
      T.trace((phi@phi.conj().T)@(chi@chi.conj().T)).real)
    return T.autograd.grad(original,v)[0].detach().numpy()

for p in (.0,.2,.35,.5,1.0):
    a,b,t,da,db,dt=sol.sol(p)
    gradient=source_gradient36(a,b,t)
    indices=[7,18+8,18+3]
    assert max(abs(np.delete(gradient,indices)))<1e-10
    assert max(abs(gradient[indices]-rhs(p,sol.sol(p))[3:,0]))<1e-10

# Necessary Gauss/current check: variations of the scalar source
# along each Hermitian su3L/su3R generator are orthogonal to the
# y profile derivative, permitting the A_y=0 ansatz at this level.
def E(i,j):
    v=np.zeros((3,3),complex);v[i,j]=1;return v
H=[]
for i in range(3):
    for j in range(i+1,3):
        H.extend([E(i,j)+E(j,i),-1j*E(i,j)+1j*E(j,i)])
H.extend([np.diag([1,-1,0]),np.diag([1,1,-2])])
for p in (.0,.21,.39,.5,1.0):
    a,b,t,da,db,dt=sol.sol(p)
    phi=a*E(2,1);chi=b*E(2,2)+t*E(1,0)
    dphi=da*E(2,1);dchi=db*E(2,2)+dt*E(1,0)
    left=[2*np.real(np.vdot(1j*h@phi,dphi)+np.vdot(1j*h@chi,dchi)) for h in H]
    right=[2*np.real(np.vdot(-1j*phi@h,dphi)+np.vdot(-1j*chi@h,dchi)) for h in H]
    assert max(abs(v) for v in left+right)<1e-10

# One conservative stability receipt ONLY WITHIN THREE-SCALAR ANSATZ.
# Piecewise-linear finite element kinetic bilinear and weighted local
# Hessian (including W'' at both ends), generalized eigenproblem.
N=80
pos=np.linspace(0,L,N+1);step=L/N
zz=sol.sol(pos)
aa,bb,tt=zz[:3]
A,B,U=sp.symbols("a b t",real=True)
Hfun=sp.lambdify((A,B,U),sp.hessian(V6(A,B,U),(A,B,U)),"numpy")
K=np.zeros((3*(N+1),3*(N+1)))
M=np.zeros_like(K)
for i in range(N+1):
    weight=.5 if i in (0,N) else 1.
    ix=np.arange(3*i,3*i+3)
    K[np.ix_(ix,ix)]+=step*weight*Hfun(aa[i],bb[i],tt[i])
    M[np.ix_(ix,ix)]+=step*weight*np.eye(3)
    if i in (0,N):
        K[3*i+2,3*i+2]+=-mu2+6*lam*tt[i]**2
for i in range(N):
    for q in range(3):
        ii,jj=3*i+q,3*(i+1)+q
        K[ii,ii]+=1/step;K[jj,jj]+=1/step
        K[ii,jj]-=1/step;K[jj,ii]-=1/step
eig=eigh(K,M,subset_by_index=(0,2),eigvals_only=True)
assert eig[0]>2.4

print("Old homogeneous t bulk force (NONZERO):",bulk_t_old)
print("Old integrated zero-mode boundary cancellation:",bdry_t_old)
print("Correct interval BVP status:",sol.message)
print("a,b,t left boundary:",z[:3,0])
print("a,b,t centre:",z[:3,200])
print("maximum scalar gradient along y:",np.max(abs(z[3:])))
print("bulk+boundary ENERGY compared to trivial EW branch:",energy)
print("3-field FEM generalized lowest eigenvalues:",eig)
print("PASS full 36-real scalar bulk gradient transverse residual and zero gauge y-current, selected points")
print("PASS nonconstant 3-field interval E-L and two-endpoint Robin BC")
print("OPEN full 18 even functional Hessian, odd KK tower, anomaly-free GS/global action and physical 5D dimensions/radion")
