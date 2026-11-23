#!/usr/bin/env python3
"""Existing Cube27 signed inverse -> arbitrary-potential switching and SI exterior.
Numerical finite-carrier check, symbolic ledger; not physical metric identification.
"""
import sympy as s
import numpy as np
from scipy.sparse import diags
from scipy.sparse.linalg import eigsh
from scipy.optimize import brentq
from itertools import combinations_with_replacement
from check_369_cube27_geometry_vs_modular_charge import CUBE
from kk_cube27_manypair_bidi import operators

def symbolic():
    t,T,eta,M=s.symbols('t T eta M',positive=True)
    u=t/T
    X=-1+2*(10*u**3-15*u**4+6*u**5)
    v=s.diff(X,t); a=s.diff(v,t)
    q=s.symbols('q'); V=s.Function('V')(q)
    force=M*a+eta*v+s.diff(V,q).subs(q,X)
    assert s.simplify(force*v-s.diff(M*v*v/2+V.subs(q,X),t)-eta*v*v)==0
    assert all(s.simplify(y.subs(t,b))==0 for y in (v,a) for b in (0,T))
    assert s.simplify(s.integrate(eta*v*v,(t,0,T))-40*eta/(7*T))==0
    R,r,K,c,G,g,a=s.symbols('R r K c G g a',positive=True)
    D=s.sqrt(6)*g*r**3/(a*c**2)
    energy=4*s.pi*K*D**2/(3*R**3)
    assert s.simplify(energy.subs(K,c**4/(8*s.pi*G))-g*g*r**6/(G*R**3*a*a))==0
    print('PASS arbitrary-potential switching ledger, endpoints, dissipated work, SI exterior energy')

def native():
    N,U,flux=3,4,1.5
    H,Q,O,S=operators(N,U,1,flux)
    z=np.array(sorted(CUBE))[:,2]
    counts=np.array([np.bincount(st,minlength=27) for st in combinations_with_replacement(range(27),N)])
    W=counts*(counts-1)/2
    assert np.allclose(W.sum(axis=1),Q.diagonal())
    assert np.allclose(W@z,S) and np.allclose(counts@z,O)
    W=np.stack([W[:,z==i].sum(axis=1) for i in (-1,0,1)],axis=1)
    z=np.arange(-1,2)
    def jet(F,q):
        eq=np.exp(-1.5*q*z)
        Hq=H+diags(U*(W@(eq-1))-F*O)
        e,w=eigsh(Hq,k=2,which='SA',tol=1e-11,v0=np.ones(H.shape[0]))
        i=np.argsort(e); e=e[i];g=w[:,i[0]]
        assert e[1]-e[0]>1e-7
        return e[0],np.vdot(g,U*(W@(-1.5*z*eq))*g).real
    F=brentq(lambda f:jet(f,1)[1]+jet(f,-1)[1]-.2,-1,0,xtol=1e-12)
    D=.1-jet(F,1)[1]
    def V(q):return (D-1)*q*q/2+q**4/4-.1*q+jet(F,q)[0]
    def force(q):return (D-1)*q+q**3-.1+jet(F,q)[1]
    def curvature(q):
        h=1e-4
        return (force(q+h)-force(q-h))/(2*h)
    assert D>0
    for q in (-1,1):
        assert abs(force(q))<1e-8 and curvature(q)>0
    q=brentq(force,-.8,.8)
    assert curvature(q)<0
    print('native',F,D,'barrier',q,'barrier heights',V(q)-V(-1),V(q)-V(1),'delta energy',V(1)-V(-1))
if __name__=='__main__':
    symbolic()
    native()
