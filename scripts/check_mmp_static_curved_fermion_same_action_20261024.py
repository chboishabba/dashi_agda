#!/usr/bin/env python3
"""One STATIC finite Wilson-Dirac spectral functional W[N(x),r(x),A_x].
It couples a round spin-c S2 mode tower to static ds2=-N(x)^2 dt^2+dx^2.
Variations w.r.t. all three source arguments use the SAME finite sea.
PAULI-VILLARS-LIKE mass subtraction here is regulator-sensitive: no claim
of 4D covariant renormalisation, full anomaly, induced Hall response,
real-time Schwinger polarization, or gravitational fixed-point closure.
"""
import math
import numpy as np
from numpy.linalg import eigvalsh

sx=np.array([[0,1],[1,0]],complex)
sz=np.diag([1.,-1.]).astype(complex)
def H(N,m,theta,L):
    M=len(N);h=L/M
    out=np.zeros((2*M,2*M),complex)
    alpha=(-1j*sx-0.75*sz)/(2*h)
    for j in range(M):
        k=(j+1)%M
        out[2*j:2*j+2,2*j:2*j+2]+=N[j]*(m[j]*sz+0.75*sz/h)
        hop=alpha*(N[j]+N[k])*.5*np.exp(1j*theta[j])
        out[2*j:2*j+2,2*k:2*k+2]+=hop
        out[2*k:2*k+2,2*j:2*j+2]+=hop.conj().T
    return out
def sea(M):return -.5*np.abs(eigvalsh(M)).sum()
def W(N,r,A,L,q=12,levels=2,regulator=7):
    total=0.
    for n in range(levels+1):
        mass=np.sqrt(n*(n+abs(q)))/r if n else np.zeros_like(r)
        degeneracy=abs(q) if n==0 else 2*(abs(q)+2*n)
        total+=degeneracy*(sea(H(N,mass,A,L))-
             sea(H(N,np.sqrt(mass**2+regulator**2),A,L)))
    return total
def derivative(f,a,j,h=1e-4):
    p=a.copy();m=a.copy();p[j]+=h;m[j]-=h
    return (f(p)-f(m))/(2*h)

M=9;L=12.;q=12;j=np.arange(M)
N=1+.13*np.sin(2*np.pi*j/M)+.07*np.cos(4*np.pi*j/M)
r=3.3+.2*np.cos(2*np.pi*j/M)
A=np.ones(M)*.37/M
rng=np.random.default_rng(109)
phase=rng.normal(size=M)*.25
Anew=np.array([A[k]+phase[k]-phase[(k+1)%M] for k in range(M)])
G=np.diag(np.repeat(np.exp(1j*phase),2))
mass=np.sqrt(1*(1+q))/r
base=H(N,mass,A,L)
cov=np.max(np.abs(H(N,mass,Anew,L)-G@base@G.conj().T))
assert cov<1e-12
assert abs(W(N,r,A,L)-W(N,r,Anew,L))<1e-9
cur=np.array([derivative(lambda u:W(N,r,u,L),A,k) for k in range(M)])
assert np.max(np.abs(cur-np.roll(cur,1)))<2e-7
dN=np.array([derivative(lambda u:W(u,r,A,L),N,k) for k in range(M)])
dr=np.array([derivative(lambda u:W(N,u,A,L),r,k) for k in range(M)])
assert np.linalg.norm(dN)>1e-5 and np.linalg.norm(dr)>1e-5
# Mixed gauge-radius Hessian symmetry from one finite functional.
h=1e-3
rp=r.copy();rm=r.copy();rp[0]+=h;rm[0]-=h
ap=A.copy();am=A.copy();ap[1]+=h;am[1]-=h
cross1=(derivative(lambda u:W(N,rp,u,L),A,1)-
        derivative(lambda u:W(N,rm,u,L),A,1))/(2*h)
cross2=(derivative(lambda u:W(N,u,ap,L),r,0)-
        derivative(lambda u:W(N,u,am,L),r,0))/(2*h)
assert abs(cross1-cross2)<2e-5
pv=[W(N,r,A,L,regulator=reg) for reg in (5,7,10)]
assert pv[0]!=pv[-1] # explicit regulator dependence, NOT renormalized
print('PASS: one finite curved static Dirac sea produces lapse/radius/current derivatives')
print('PASS: U1 gauge Ward and cross derivative reciprocity')
print('OPEN: regulator-independent 4D renormalization, Hall/dynamic current and coupled Einstein fixed point')
