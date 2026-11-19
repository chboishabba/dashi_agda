#!/usr/bin/env python3
"""Exact full P33 side-four selected-constraint bordered trace.
Native flat configured scalar Green and 12 component-sum rows. Gauge transport
of this finite pair is tested, NOT identified with CMP98 Eq124 or CMP109 measure.
Integer low-rank derivative factors; no dense 3084-square inverse or derivative.
"""
from fractions import Fraction as F
from math import lcm
import numpy as np
import sympy as sp
from check_ym_p33_configured_contractions_20261119 import SITES,N,O,diff,green
from check_ym_p33_fourier_vertices_20261119 import shift

M=12*N; B=M+12; idx={x:i for i,x in enumerate(SITES)}
D=lcm(N,*(green(x).denominator for x in SITES))
# A0 = scalar Laplacian + mean; Q0 = twelve original component sums.
L=np.eye(N,dtype=np.int64)*8
for i,x in enumerate(SITES):
    for a in range(4):
        j=idx[shift(x,a)]; L[i,j]-=1;L[j,i]-=1
Abar=N*L+1
Gcbar=np.array([[int(D*(green(diff(x,y))-F(1,N))) for y in SITES] for x in SITES],dtype=np.int64)
assert np.array_equal(Abar@Gcbar, D*(N*np.eye(N,dtype=np.int64)-1))
assert np.all(Gcbar.sum(axis=0)==0)

def K_action(X, inverse=False):
    """N*K or D*K^-1 applied to a batch of columns, exact integers."""
    V=X[:M].reshape(12,N,-1); W=X[M:]; sums=V.sum(axis=1)
    if inverse:
        Y=Gcbar@V+(D//N)*W[:,None,:]
        Z=(D//N)*(sums-W)
    else:
        Y=Abar@V+N*W[:,None,:]
        Z=N*sums
    return np.concatenate((Y.reshape(M,-1), Z),axis=0)

def basis(ids):
    E=np.zeros((B,len(ids)),dtype=np.int64)
    E[ids, np.arange(len(ids))]=1
    return E

# Exact native block inverse on all coordinate types, by all scalar columns
# in one color/direction plus identical component replicas, and multiplier.
E=basis(list(range(N))+[M]);assert np.array_equal(K_action(K_action(E), True),N*D*E)
assert np.array_equal(K_action(K_action(E, True)),N*D*E)

def generator(site, colors=(1,2)):
    # Right endpoint tangent: four incoming bonds at the selected gauge site.
    # Quaternion adjoint generator has magnitude 2, not Pauli-half 1.
    ids=[]
    for mu in range(4):
        x=tuple((v-(j==mu))%4 for j,v in enumerate(site))
        for c in colors: ids.append((3*mu+c)*N+idx[x])
    E=basis(ids); J=np.kron(np.eye(4,dtype=np.int64),np.array([[0,-2],[2,0]],dtype=np.int64))
    return E,J

def commutator(E,J,act):
    # [R,H]=E J E^T H-H E J E^T; H symmetric, R skew.
    Y=act(E)
    return np.concatenate((E,-Y),axis=1), np.concatenate((J@Y.T,J@E.T),axis=0)

def action(f,X):return f[0]@(f[1]@X)
def trace_product(V,U):
    # Cast before multiplication: no fixed-width overflow in final trace.
    return sum(int(a)*int(b) for a,b in zip(V.flat,U.T.flat))
def trace_one(f):
    U,V=f; return F(trace_product(V,K_action(U,True)),N*D)
def trace_two(f,g):
    U,V=f; W,Z=g
    a=V@K_action(W,True); b=Z@K_action(U,True)
    return F(trace_product(a,b),(N*D)**2)

def gauge_pair(site1,site2,fixed=False):
    E,J=generator(site1); F0,J0=generator(site2)
    def base_action(X):
        if not fixed:return K_action(X)
        # Only A transported: freeze Q to expose missing constraint response.
        X=X.copy();X[M:]=0
        Y=K_action(X);Y[M:]=0
        return Y
    ds=commutator(E,J,base_action);dt=commutator(F0,J0,base_action)
    dst=commutator(E,J,lambda X:action(dt,X))
    tad=trace_one(dst);bubble=trace_two(ds,dt)
    return tad,bubble,(tad-bubble)/2

def normal_motion():
    # Independent physical-size rank-one normal constraint motion: change the
    # first row by (s+t)(e_x-e_y)^T while holding the configured A fixed.
    # This is a diagnostic family, NOT the CMP98 transported path operator.
    v=basis([0]) - basis([idx[(1,0,0,0)]])
    e=basis([M]); U=np.concatenate((v,e),axis=1)
    V=N*np.concatenate((e.T,v.T),axis=0)
    f=(U,V)
    k_mixed=-trace_two(f,f)
    gram_mixed=F(4,N) # ||v||^2=2 and mixed second derivative of (s+t)^2
    induced=(k_mixed-gram_mixed)/2
    delta=k_mixed/2
    # Schur complement using the independently evaluated scalar G kernel.
    schur=2*(green(O)-green((1,0,0,0)))
    assert delta==schur/N
    assert induced==(schur-2)/N
    assert induced!=0 and delta!=0
    print('normal row motion: bordered vs Schur exact; induced=',induced,'delta=',delta)

def main():
    print('P33 state/multiplier dimensions:',M,12,'inverse scaling',D)
    print('PASS 256 scalar and 257 representative bordered columns, both inverse orders')
    for site in [O,(1,0,0,0),(2,0,0,0),(0,1,1,0)]:
        t,b,r=gauge_pair(O,site);assert r==0
        print('transport Q',site,'T=',t,'B=',b,'mixed=',r)
    normal_motion()
    t,b,r=gauge_pair(O,O, fixed=True);assert r!=0
    print('freeze Q negative control T=',t,'B=',b,'mixed=',r)
    # Row scaling does not change ker Q or induced-volume Gaussian, but
    # delta(Qx) changes integration normalization. Distinguish source measures.
    s,t=sp.symbols('s t'); scale=1+s+t
    delta_debt=sp.diff(12*sp.log(scale),s,t).subs({s:0,t:0});assert delta_debt==-12
    print('measure row-scaling mixed delta-vs-induced difference:',delta_debt)
    print('OPEN original CMP98 Eq124 transported family, CMP109 measure, physical beta')
if __name__=='__main__':main()
