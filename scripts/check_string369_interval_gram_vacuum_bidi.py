#!/usr/bin/env python3
"""Original #1241 nonconstant interval V6 BVP, #1531 oriented Gram.
Compare canonical, temporal-only Gram and common spatial/temporal Gram.
Selected dimensionless restricted three-real-field action, not physical
CY metric or actual compactification scale. Inherited rho, no Higgs fit.
"""
import numpy as np
from scipy.integrate import solve_bvp
from scipy.linalg import eigh
mu=3.00090774; lam=4.; r=.201971182865772; D=1-r*r
G=np.array([[1,r,0],[r,1,0],[0,0,D]])
def rhs(y,u):
 a,b,t,da,db,dt=u
 return np.vstack((da,db,dt,4*a**3+2*a*t*t-4*a,4*b**3+8*b*t*t-4*b,2*a*a*t+8*b*b*t+4*t**3-4*t))
def bc(l,h):return np.array([l[3],l[4],l[5]+mu*l[2]-2*lam*l[2]**3,h[3],h[4],h[5]-mu*h[2]+2*lam*h[2]**3])
grid=np.linspace(0,1,101); t=.33*np.cosh(2*(grid-.5))/np.cosh(1); init=np.vstack((np.sqrt(1-t*t/2),np.sqrt(1-2*t*t),t,0*t,0*t,.66*np.sinh(2*(grid-.5))/np.cosh(1)))
sol=solve_bvp(rhs,bc,grid,init,tol=2e-9,max_nodes=12000); assert sol.status==0
print('vacuum',sol.sol([0,.5,1])[:3])
def fem(N):
 p=np.linspace(0,1,N+1); step=1/N; K=np.zeros((3*(N+1),)*2); M=K.copy(); MG=K.copy()
 for i,(a,b,t) in enumerate(sol.sol(p)[:3].T):
  H=np.array([[12*a*a+2*t*t-4,0,4*a*t],[0,12*b*b+8*t*t-4,16*b*t],[4*a*t,16*b*t,2*a*a+8*b*b+12*t*t-4]])
  ix=slice(3*i,3*i+3); w=step*(.5 if i in (0,N) else 1)
  K[ix,ix]+=w*H; M[ix,ix]+=w*np.eye(3); MG[ix,ix]+=w*G
  if i in (0,N):K[3*i+2,3*i+2]+=-mu+6*lam*t*t
 for i in range(N):
  ix=np.arange(3*i,3*i+6);K[np.ix_(ix,ix)]+=np.kron([[1,-1],[-1,1]],np.eye(3))/step
 return K,M,MG
for N in [32,64,128]:
 K,M,MG=fem(N); a=eigh(K,M,subset_by_index=(0,5),eigvals_only=True); b=eigh(K,MG,subset_by_index=(0,5),eigvals_only=True);print(N,a,b,'ratios',np.sqrt(b/a))
m0=(1+np.sqrt(5))/2*246.22/np.pi
print('m0',m0,'interval mass',m0*np.sqrt(b[0]/a[0]),'cube',m0*D**(1/3),'target ratio',125.065/m0)
print('conditional spectra GeV',m0*np.sqrt(a/a[0]),m0*np.sqrt(b/a[0]))
def rhsG(y,u):
 f=rhs(y,u);return np.vstack((f[:3],np.linalg.solve(G,f[3:])))
def bcG(l,h):
 return np.r_[G@l[3:]+[0,0,mu*l[2]-2*lam*l[2]**3],G@h[3:]+[0,0,-mu*h[2]+2*lam*h[2]**3]]
sol=solve_bvp(rhsG,bcG,grid,sol.sol(grid),tol=2e-9,max_nodes=12000);assert sol.status==0
print('joint metric vacuum',sol.sol([0,.5,1])[:3])
for N in [32,64,128]:
 K,M,MG=fem(N);step=1/N
 for i in range(N):
  ix=np.arange(3*i,3*i+6);K[np.ix_(ix,ix)]+=np.kron([[1,-1],[-1,1]],G-np.eye(3))/step
 c=eigh(K,MG,subset_by_index=(0,5),eigvals_only=True);print('joint',N,c)
print('joint conditional masses',m0*np.sqrt(c/a[0]))
