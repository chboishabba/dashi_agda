#!/usr/bin/env python3
"""Independent curvature contraction and three-grid G3 constraint diagnostics.
Finite sampled central domain only, not continuum existence or exterior acceptance.
"""
import argparse
import numpy as np
from scipy.interpolate import RegularGridInterpolator
import check_hopf369_br240_metric_history as d


def curvature(g, first, second):
    """Direct pointwise index-loop Ricci and lowered harmonic gauge derivative.
    first[k,a,b]=partial_k g_ab; second[k,l,a,b]=partial_k partial_l g_ab.
    No reuse of BR240 einsum index contractions.
    """
    I=np.linalg.inv(g); N=range(5)
    di=np.zeros((5,5,5)); L=np.zeros((5,5,5)); dl=np.zeros((5,5,5,5))
    for a in N:
        for b in N:
            for c in N:
                di[a,b,c]=-sum(I[b,r]*first[a,r,t]*I[t,c] for r in N for t in N)
                L[a,b,c]=(first[b,a,c]+first[c,a,b]-first[a,b,c])/2
                for k in N: dl[k,a,b,c]=(second[k,b,a,c]+second[k,c,a,b]-second[k,a,b,c])/2
    G=np.zeros_like(L); DG=np.zeros_like(dl); C=np.zeros(5); DC=np.zeros((5,5))
    for a in N:
        for b in N:
            for c in N:
                G[a,b,c]=sum(I[a,e]*L[e,b,c] for e in N)
                for k in N: DG[k,a,b,c]=sum(di[k,a,e]*L[e,b,c]+I[a,e]*dl[k,e,b,c] for e in N)
        C[a]=sum(I[b,c]*L[a,b,c] for b in N for c in N)
        for k in N: DC[k,a]=sum(di[k,b,c]*L[a,b,c]+I[b,c]*dl[k,a,b,c] for b in N for c in N)
    R=np.zeros((5,5)); covC=np.zeros((5,5))
    for a in N:
        for b in N:
            R[a,b]=sum(DG[k,k,a,b]-DG[b,k,a,k]+sum(G[k,k,e]*G[e,a,b]-G[k,b,e]*G[e,a,k] for e in N) for k in N)
            covC[a,b]=DC[a,b]-sum(G[k,a,b]*C[k] for k in N)
    return R,C,covC


def random_jets():
    rng=np.random.default_rng(369); worst=0.; principal_worst=0.; gauge_worst=0.
    for k in range(12):
        def sym(x):return (x+x.swapaxes(-1,-2))/2
        g=np.diag([-1.,1.,1.,1.,1.])+sym(rng.normal(size=(5,5)))*.08
        f=sym(rng.normal(size=(5,5,5)))*.15; f[4]=0
        h=sym(rng.normal(size=(5,5,5,5)))*.15; h=(h+h.swapaxes(0,1))/2;h[4]=0;h[:,4]=0
        # Sample polynomial jets at center; centered differences exact for quadratic.
        dx=.125; x=np.arange(-2,3)*dx; X=np.stack(np.meshgrid(x,x,x,indexing='ij'),axis=-1)
        gg=g+np.einsum('...i,iab->...ab',X,f[1:4])+np.einsum('...i,...j,ijab->...ab',X,X,h[1:4,1:4])/2
        vv=f[0]+np.einsum('...i,iab->...ab',X,h[0,1:4]); mid=(2,2,2)
        a=d.acceleration(gg,vv,dx)[mid]
        h[0,0]=a
        R,C,DC=curvature(g,f,h); residual=R-(DC+DC.T)/2
        err=np.max(abs(residual)); worst=max(worst,err)
        gauge_worst=max(gauge_worst,np.max(abs(C-d.jets(gg,vv,dx)[3][mid])))
        # Independent check of the principal coefficient against zero second jets.
        R0,C0,D0=curvature(g,f,np.zeros_like(h)); Q=R0-(D0+D0.T)/2
        principal=np.einsum('ij,ijab->ab',np.linalg.inv(g),h)
        principal_worst=max(principal_worst,np.max(abs(residual-Q+principal/2)))
        assert np.max(abs(R-R.T))<1e-12
    assert max(worst,principal_worst,gauge_worst)<1e-11
    print('BR242 PASS 12 arbitrary Lorentzian circle-invariant metric jets; reduced residual',worst,'principal residual',principal_worst,'gauge residual',gauge_worst)


def history(n):
    g,v,dx=d.initial(n); steps=int(round(.12/(.1*dx)));dt=.12/steps
    def rhs(g,v):
        a=d.acceleration(g,v,dx);vv=v.copy()
        for i in range(3):
            for j in (0,-1):
                idx=[slice(None)]*3;idx[i]=j;a[tuple(idx)]=0;vv[tuple(idx)]=0
        return vv,a
    def inspect(g,v):
        first=d.jets(g,v,dx)[0]; a=d.acceleration(g,v,dx); m=n//2
        # One common physical point (origin), direct tensor contractions.
        second=np.zeros((5,5,5,5)); second[0,0]=a[m,m,m]
        for i in range(1,4):
            plus=[m]*3;minus=[m]*3;plus[i-1]+=1;minus[i-1]-=1
            second[0,i]=second[i,0]=(v[tuple(plus)]-v[tuple(minus)])/(2*dx)
            second[i,i]=(g[tuple(plus)]-2*g[m,m,m]+g[tuple(minus)])/dx**2
            for j in range(1,i):
                acc=np.zeros((5,5))
                for s in (-1,1):
                    for t in (-1,1):
                        p=[m]*3;p[i-1]+=s;p[j-1]+=t;acc+=s*t*g[tuple(p)]
                second[i,j]=second[j,i]=acc/(4*dx**2)
        gg=g[m,m,m]; I=np.linalg.inv(gg);R,C,DC=curvature(gg,first[m,m,m],second)
        E=R-gg*np.sum(I*R)/2;normal=-I[:,0]/np.sqrt(-I[0,0]); ham=2*normal@E@normal;mom=normal@E[:,1:]
        reduced=np.max(abs(R-(DC+DC.T)/2)); assert reduced<1e-10
        return float(abs(ham)),float(np.max(abs(mom))),float(np.max(abs(C))),float(reduced)
    initial=inspect(g,v)
    for _ in range(steps):
        u,a=rhs(g,v);w,b=rhs(g+dt*u/2,v+dt*a/2);g+=dt*w;v+=dt*b
        assert np.max(np.linalg.eigvalsh(g)[...,0])<0 and np.min(np.linalg.eigvalsh(g)[...,1])>0
    final=inspect(g,v)
    grid=np.linspace(-1.5,1.5,n); coords=np.linspace(-.6,.6,5); pts=np.stack(np.meshgrid(coords,coords,coords,indexing='ij'),axis=-1)
    C=d.jets(g,v,dx)[3]; common=RegularGridInterpolator((grid,)*3,C)(pts); readout=RegularGridInterpolator((grid,)*3,g)(pts)
    print('BR243',n,'dt',dt,'initial (Hamiltonian,momentum,gauge,reduced)',initial,'final',final,'common sampled gauge',np.max(abs(common)),flush=True)
    return readout,float(np.max(abs(common))),initial,final


def grids():
    records=[history(n) for n in (11,17,23)]
    a,b,c=[r[0] for r in records];e0=np.max(abs(a-b));e1=np.max(abs(b-c))
    print('BR244 common physical samples intergrid metric differences',e0,e1,'ratio',e1/e0,'gauge',[r[1] for r in records],flush=True)
    # Record nonmonotonicity, do not turn it into a fake convergence pass.
    assert np.all(np.isfinite([e0,e1,*[r[1] for r in records]])) and e0>0
    print('BR244 finite diagnostics completed; no continuum convergence certificate')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['jets','grids'],required=True);globals()[{'jets':'random_jets','grids':'grids'}[p.parse_args().part]]()
