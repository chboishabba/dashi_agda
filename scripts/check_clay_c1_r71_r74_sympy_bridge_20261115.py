#!/usr/bin/env python3
"""Clay #1499 C1: exact R71/R74 real-atom identity and classical R854 ODE cut.

SymPy proves each ordered triad coefficient identity for arbitrary symbolic
values and both reality signs. Finite-cutoff checks are independent tests, not
Agda proof terms. Requires sympy; no CI, Agda, floats or trust in a status flag.
"""
from fractions import Fraction as Q
from itertools import product
import sympy as s

def symbolic():
    k=s.symbols('kx ky kz'); q=s.symbols('qx qy qz')
    v,ep,eq=s.symbols('invnorm2 epsp epsq')
    a=s.symbols('a0:3'); b=s.symbols('b0:3')
    c=s.symbols('c0:3'); d=s.symbols('d0:3')
    U=[a[t]+s.I*ep*b[t] for t in range(3)]
    V=[c[t]+s.I*eq*d[t] for t in range(3)]
    dot=sum(q[t]*U[t] for t in range(3))
    for j in range(3):
        P=[int(j==t)-v*k[j]*k[t] for t in range(3)]
        physical=-s.I*dot*sum(P[t]*V[t] for t in range(3))
        real=sum(q[l]*P[t]*(a[l]*eq*d[t]+ep*b[l]*c[t])
                 for l,t in product(range(3),repeat=2))
        imag=sum(q[l]*P[t]*(ep*eq*b[l]*d[t]-a[l]*c[t])
                 for l,t in product(range(3),repeat=2))
        assert s.expand(physical-real-s.I*imag)==0
    assert s.expand(dot*V[0]+s.I*dot*V[0])!=0 # wrong sign control

def modes(n):
    return [m for m in product(range(-n,n+1),repeat=3) if any(m)]
def representative(m):
    if not any(m):return None,0
    sign=1 if next(x for x in m if x)>0 else -1
    return tuple(sign*x for x in m),sign
def u(state,m,j):
    rep,sign=representative(m)
    if sign==0:return (Q(0),Q(0))
    return (state.get((rep,j,0),Q(0)),sign*state.get((rep,j,1),Q(0)))
def add(a,b):return a[0]+b[0],a[1]+b[1]
def mul(a,b):return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def scale(a,b):return a*b[0],a*b[1]
def negative_i(a):return a[1],-a[0]
def rhs(state,k,j,n=4):
    sq=sum(x*x for x in k)
    total=scale(-sq,u(state,k,j))
    for p in modes(n):
        q=tuple(k[t]-p[t] for t in range(3))
        if not any(q) or any(abs(t)>n for t in q):continue
        dot=(Q(0),Q(0)); projected=(Q(0),Q(0))
        for t in range(3):
            dot=add(dot,scale(q[t],u(state,p,t)))
            projected=add(projected,scale(Q(int(j==t))-Q(k[j]*k[t],sq),u(state,q,t)))
        total=add(total,negative_i(mul(dot,projected)))
    return total

def initial_snapshot_and_forcing():
    state={}; U={
        (0,4,0):[(2,2),(0,0),(2,2)],
        (3,0,0):[(0,0),(2,2),(-2,-1)],
        (3,4,0):[(0,6),(0,Q(-9,2)),(-2,2)]}
    for m,vec in U.items():
        for j,(re,im) in enumerate(vec):
            state[m,j,0]=Q(re);state[m,j,1]=Q(im)
    expected={
        (-3,-4,0):[(Q(224,25),0),(-Q(168,25),0),(14,-6)],
        (-3,0,0):[(0,0),(-27,-27),(60,36)],
        (-3,4,0):[(0,-Q(224,25)),(0,-Q(168,25)),(6,-50)],
        (0,-4,0):[(48,48),(0,0),(68,18)],
        (0,4,0):[(48,-48),(0,0),(68,-18)],
        (3,-4,0):[(0,Q(224,25)),(0,Q(168,25)),(6,50)],
        (3,0,0):[(0,0),(-27,27),(60,-36)],
        (3,4,0):[(Q(224,25),0),(-Q(168,25),0),(14,6)]}
    assert max(abs(x) for x in state.values())==6
    for k,components in expected.items():
        for j,component in enumerate(components):
            # R71 total RHS = viscous + projected nonlinearity.
            projected=add(rhs(state,k,j),scale(sum(x*x for x in k),u(state,k,j)))
            assert projected==tuple(map(Q,component)),(k,j,projected,component)
    return len(expected)*3

def horizon():
    N=4; M=12; nmodes=len(modes(N))
    assert nmodes==728
    for k in modes(N):
        sq=sum(x*x for x in k)
        for j in range(3):
            row=sum(abs(Q(int(j==t))-Q(k[j]*k[t],sq)) for t in range(3))
            assert row<=2,(k,j,row)
    # Re/Im component of each triad <= 2*(3*N*M)*(2*M)=48*M^2.
    K=nmodes*2*(3*N*M)*(2*M)+3*N*N*M
    T=Q(226189,3938540454339300631433585885184)
    assert K==5032512 and K*T<6
    # Classical Picard-Lindelof on R^(6*364), with first-exit
    # ||x(t)-x0||_infty <= K*t < 6 on [0,T], gives existence on T.
    return K,T

if __name__=='__main__':
    symbolic(); print('PASS: universal symbolic R71 ordered triad -> real quadratic atom identity')
    print('PASS: original R829/R836 exact projected-forcing real components:',initial_snapshot_and_forcing())
    K,T=horizon(); print('PASS: original cutoff-four R71 bound K=',K,'and K*T<6; T=',T)
    print('C1 classical mathematical seam discharged; Agda native proof and R408/C2 remain open')
