#!/usr/bin/env python3
"""Backward signed inverse on the original Cube27 Hamiltonian.

Retains original prescribed U_i(q)=U exp(-3 q z_i/2), not a physical
CY/radion identification. Fixed normalized flux shift A=1, bias B+b=.1,
geometric quartic gamma=1. Grid-bracketed roots, not exhaustive proof.
"""
from itertools import combinations_with_replacement, product
import numpy as np
from scipy.sparse import diags
from scipy.sparse.linalg import eigsh, cg, LinearOperator
from scipy.optimize import brentq
from check_369_cube27_geometry_vs_modular_charge import CUBE
from kk_cube27_manypair_bidi import operators
from kk_cube27_nonlinear_weld import weld

def quartic_inverse(N,U,flux,bias=.1,A=1.,gamma=1.):
    chi,beta,m=weld(N,U,flux)
    assert chi>0 and beta>=0
    l=m/chi
    assert abs(l)>1e-12
    p=bias/l
    d=brentq(lambda d:d*(1/chi+beta*(3*p*p+d*d))+l,-100,100)
    pp,pm=p+d,p-d
    F=lambda P,X:P/chi+beta*P**3+l*X
    D=lambda P,X:A-gamma+(bias-l*P)/X
    C=lambda P:1/chi+3*beta*P*P
    K=lambda P,X:(bias-l*P)/X+2*gamma-l*l/C(P)
    assert abs(F(pp,1)-F(pm,-1))<1e-8
    assert abs(D(pp,1)-D(pm,-1))<1e-8
    return dict(chi=chi,beta=beta,m=m,drive=F(pp,1),stiffness=D(pp,1),
                P=(pp,pm),curvature=(K(pp,1),K(pm,-1)),
                within_bound=max(abs(pp),abs(pm))<=N)

def full_inverse(N,U,flux,bias=.1,A=1.,gamma=1.):
    H,Q,O,S=operators(N,U,1,flux)
    z=np.array(sorted(CUBE))[:,2]
    states=list(combinations_with_replacement(range(len(z)),N))
    counts=np.array([np.bincount(st,minlength=len(z)) for st in states])
    weights=counts*(counts-1)/2
    # Same producer basis/order and derivative at origin, not a new carrier.
    assert np.allclose(weights.sum(axis=1),Q.diagonal())
    assert np.allclose(counts@z,O)
    assert np.allclose(weights@z,S)
    def jet(F,q,second=False):
        eq=np.exp(-1.5*q*z)
        Hq=H+diags(U*(weights@(eq-1))-F*O)
        e,w=eigsh(Hq,k=2,which='SA',tol=1e-11,v0=np.ones(H.shape[0]))
        i=np.argsort(e);e=e[i];g=w[:,i[0]]
        gap=e[1]-e[0]
        assert gap>1e-7
        a=U*(weights@(-1.5*z*eq))
        val=np.vdot(g,a*g).real
        P=np.vdot(g,O*g).real
        if not second:return val,P
        b=U*(weights@(2.25*z*z*eq))
        rhs=a*g-g*val
        R=LinearOperator(H.shape,matvec=lambda x:Hq@x-e[0]*x+g*np.vdot(g,x),dtype=complex)
        y,info=cg(R,rhs,rtol=1e-10,maxiter=2000)
        assert info==0
        return val,P,np.vdot(g,b*g).real-2*np.vdot(rhs,y).real,gap
    def match(F):return jet(F,1)[0]+jet(F,-1)[0]-2*bias
    grid=np.linspace(-8,8,17)
    vals=[match(F) for F in grid]
    roots=[float(F) for F,v in zip(grid,vals) if abs(v)<1e-12]
    roots += [brentq(match,x,y,xtol=1e-9)
              for x,y,v,w in zip(grid[:-1],grid[1:],vals[:-1],vals[1:])
              if v*w<0]
    results=[]
    for F in roots:
        a,p,c,gap=jet(F,1,True)
        b,m,d,gap2=jet(F,-1,True)
        D=A-gamma+bias-a
        assert abs(D-(A-gamma-bias+b))<1e-8
        Kp= D-A+3*gamma+c
        Km= D-A+3*gamma+d
        # Independent finite difference of the Hellmann-Feynman force.
        for q,curv in ((1,c),(-1,d)):
            h=1e-4
            fd=(jet(F,q+h)[0]-jet(F,q-h)[0])/(2*h)
            assert abs(fd-curv)<2e-5
        results.append(dict(drive=F,stiffness=D,P=(p,m),
                        curvature=(Kp,Km),gap=(gap,gap2),
                        stable=min(Kp,Km)>0,within_bound=max(abs(p),abs(m))<=N+1e-10))
    return results

if __name__=='__main__':
    for N,U,flux in product((2,3),(1,4),(0,1.5)):
        a=quartic_inverse(N,U,flux)
        b=full_inverse(N,U,flux)
        print(N,U,flux,'quartic',a,'finite amplitude',b,flush=True)
        assert any(x['stable'] and x['within_bound'] for x in b)
    print('PASS selected finite-amplitude shared-control fixtures; no physical normalization claim')
