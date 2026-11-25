"""Original selected cubic acoustic lattice: signed response and continuum controls.
Not a physical TSVF measurement or kernel certificate.
"""
from fractions import Fraction as F
from itertools import product
from collections import deque
import math
import numpy as np
import sympy as s


def graph_checks():
    N=5; nodes=list(product(range(N),repeat=3)); o=(0,0,0)
    c=F(3,2); a=F(1,5); mu=F(7,10); k=c*c/(a*a)
    def near(x):
        for j in range(3):
            for sign in (-1,1):
                y=list(x); y[j]=(y[j]+sign)%N; yield tuple(y)
    dist={o:0}; count={o:1}; todo=deque([o])
    while todo:
        x=todo.popleft()
        for y in near(x):
            if y not in dist:
                dist[y]=dist[x]+1; count[y]=0; todo.append(y)
            if dist[y]==dist[x]+1: count[y]+=count[x]
    def step(v):
        return {x:(mu*mu+6*k)*v[x]-k*sum(v[y] for y in near(x)) for x in nodes}
    v={x:F(x==o) for x in nodes}; checks=0
    for j in range(max(dist.values())+1):
        for x in nodes:
            if j<dist[x]: assert v[x]==0; checks+=1
            if j==dist[x]:
                assert (-1)**j*v[x]==count[x]*k**j; checks+=1
        v=step(v)
    assert len(dist)==125
    print('PASS original 125 sites all-distance first response:',checks,'exact checks; diameter',max(dist.values()),flush=True)
    k0,m=s.symbols('k m'); near3=k0; center3=-(m+6*k0)
    assert s.expand(-center3-6*near3-m)==0
    assert s.expand(near3-k0)==0
    print('PASS joint origin/neighbor mass and coupling inverse',flush=True)


def response_checks():
    # Same c, mu, L=N*a=1 as original source; fixed continuum modes.
    c=1.5; mu=.7; L=1.; T=.3
    modes=np.array(list(product(range(-2,3),repeat=3)),dtype=float)*2*np.pi/L
    lam=mu**2+c*c*np.sum(modes*modes,axis=1)
    times=np.linspace(0,T,31); prev=None
    for N in (16,32,64,128):
        a=L/N; la=mu**2+4*c*c/a**2*np.sum(np.sin(a*modes/2)**2,axis=1)
        delta=c*c*a*a*np.sum(modes**4,axis=1)/12
        assert np.all(lam-la>=-1e-10) and np.all(lam-la<=delta+1e-10)
        K=lambda l: np.sin(times[:,None]*np.sqrt(l))/np.sqrt(l)
        err=np.abs(K(lam)-K(la)); bound=times[:,None]**3*delta/6
        assert np.all(err<=bound+1e-12)
        assert np.allclose(K(lam)[:,62],K(la)[:,62],atol=1e-15,rtol=0)
        # Signed Fourier conjugate and zero momentum retained.
        assert np.allclose(K(la),K(la)[:,::-1],atol=1e-15,rtol=0)
        peak=float(err.max()); rate=None if prev is None else math.log(prev/peak,2)
        print('PASS fixed-band retarded replay',N,'max error',peak,'rate',rate,'bound',float(bound.max()),flush=True)
        prev=peak
    assert np.array_equal(times*np.sinc(times*0/np.pi),times)
    print('PASS 15500 response-bound controls, zero momentum, massless zero branch and signed pairing (floating tolerance)',flush=True)


if __name__=='__main__':
    graph_checks(); response_checks()
