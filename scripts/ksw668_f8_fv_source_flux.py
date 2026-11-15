#!/usr/bin/env python3
"""Exact finite-volume original a=t compact TT multipole SOURCE integrals.

For the ORIGINAL C-infinity bump exp(1-1/(1-u*u)) on 0<=u<1,
the angular TT source coefficients S_l/u^l have weighted moments
u^(2+2l). l=0,2 have exact total zero moments; l=4 moment equals
27 integral u² f(u)du. Supports finite-volume source independently
of fourth-derivative centre sampling. Does NOT bound the retarded Weyl.
"""
import functools
import numpy as np
import sympy as sp
from scipy.integrate import quad

@functools.lru_cache(maxsize=1)
def primitives():
    u=sp.symbols('u',positive=True)
    f=sp.exp(1-1/(1-u*u))
    d=[f]+[sp.diff(f,u,n) for n in range(1,4)]
    p0=sp.Rational(2,5)*(u*u*d[3]+2*u*d[2]-2*d[1])
    p2=sp.Rational(4,7)*(u**4*d[3]-3*u**3*d[2]+3*u**2*d[1])
    p4=(u**6*d[3]-12*u**5*d[2]+75*u**4*d[1]-315*u**3*f)/35
    return tuple(sp.lambdify(u,sp.factor(p),'numpy') for p in (p0,p2,p4))

def compact_bump(u):
    if u<=0:return 1.
    if u>=1:return 0.
    return float(np.exp(1-1/(1-u*u)))

def cell_mass(ell,a,b):
    if not (0<=a<=b<=1 and ell in (0,2,4)):raise ValueError('scaled finite cell')
    p=primitives()[ell//2]
    lo=0. if a==0 else float(p(a))
    hi=0. if b==1 else float(p(b))
    if ell==4:
        rest,_=quad(lambda u:27*u*u*compact_bump(u),a,b,
                    epsabs=1e-11,epsrel=1e-11,limit=150)
        return hi-lo+rest
    return hi-lo

def exact_cell_averages(eps,rgrid,dr):
    if eps<=0 or dr<=0:raise ValueError('positive source scale')
    out=np.zeros((3,len(rgrid)))
    for j,r in enumerate(rgrid):
        a=max(0.,r-dr/2)
        b=min(eps,r+dr/2)
        if b<=a:continue
        for q,ell in enumerate((0,2,4)):
            d=3+2*ell
            mass=(eps**d)*cell_mass(ell,a/eps,b/eps)
            volume=((r+dr/2)**d-a**d)/d
            out[q,j]=mass/volume
    return out

def total_scaled_moments():
    norm,_=quad(lambda u:u*u*compact_bump(u),0,1,epsabs=1e-13)
    return dict(l0=cell_mass(0,0,1),l2=cell_mass(2,0,1),
                l4=cell_mass(4,0,1),l4_analytic=27*norm)

if __name__=='__main__':
    import json
    print(json.dumps(total_scaled_moments(),indent=2))
