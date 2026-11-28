#!/usr/bin/env python3
"""BR245-247: subsidiary initial weld and independent temporal metric jets.
Finite sampled diagnostics; no homogeneous continuum propagation claim.
"""
import argparse
import numpy as np
import sympy as s
from check_hopf369_br240_metric_history import initial, acceleration, jets
from check_hopf369_br242_244_constraint_history import curvature


def initial_weld():
    eta=s.diag(-1,1,1,1,1)
    a=s.Matrix(1,5,s.symbols('a:5')); D=s.zeros(5); D[0,:]=a
    E=s.Matrix(5,5,lambda i,j:s.Symbol('e%d%d'%tuple(sorted((i,j)))))
    R=E+(D+D.T)/2; G=R-eta*s.trace(eta*R)/2
    assert s.expand(2*G[0,0]-a[0]-2*E[0,0]-s.trace(eta*E))==0
    for i in range(1,5): assert s.expand(2*G[0,i]-a[i]-2*E[0,i])==0
    # Negative control: a reduced residual can hide nonzero normal gauge jet.
    assert (2*G[0,0]).subs({E[0,0]:-a[0],**{E[i,i]:0 for i in range(1,5)}})==0
    print('BR245 PASS exact normal gauge jet, including nonzero reduced residual correction')


def history(n):
    g,v,dx=initial(n); steps=int(round(.12/(.1*dx))); dt=.12/steps
    def rhs(g,v):
        a=acceleration(g,v,dx); vv=v.copy()
        for i in range(3):
            for j in (0,-1):
                idx=[slice(None)]*3;idx[i]=j;a[tuple(idx)]=0;vv[tuple(idx)]=0
        return vv,a
    old=g.copy(); states=[old]
    for _ in range(steps):
        u,a=rhs(g,v); w,b=rhs(g+dt*u/2,v+dt*a/2);g+=dt*w;v+=dt*b
        assert np.linalg.eigvalsh(g)[...,0].max()<0 and np.linalg.eigvalsh(g)[...,1].min()>0
        states.append(g.copy())
    # Common coordinate sites: origin and off-centre points closest to +/- .3.
    m=n//2; k=max(1,round(.3/dx)); points=[(m,m,m)]
    for i in range(3):
        for sign in (-1,1):
            p=[m]*3;p[i]+=sign*k;points.append(tuple(p))
    points.append((m+k,m-k,m+k))
    # Last interior time: time jets from snapshots only, no acceleration call.
    gm,g,gp=states[-3:]; v=(gp-gm)/(2*dt); acc=(gp-2*g+gm)/dt**2
    d=jets(g,v,dx)[0]; maxima=np.zeros(4)
    for p in points:
        second=np.zeros((5,5,5,5));second[0,0]=acc[p]
        for i in range(1,4):
            plus=list(p);minus=list(p);plus[i-1]+=1;minus[i-1]-=1
            second[0,i]=second[i,0]=(v[tuple(plus)]-v[tuple(minus)])/(2*dx)
            second[i,i]=(g[tuple(plus)]-2*g[p]+g[tuple(minus)])/dx**2
            for j in range(1,i):
                qsum=np.zeros((5,5))
                for a in (-1,1):
                    for b in (-1,1):
                        q=list(p);q[i-1]+=a;q[j-1]+=b;qsum+=a*b*g[tuple(q)]
                second[i,j]=second[j,i]=qsum/(4*dx**2)
        gg=g[p]; I=np.linalg.inv(gg); R,C,DC=curvature(gg,d[p],second)
        G=R-gg*np.sum(I*R)/2; normal=-I[:,0]/np.sqrt(-I[0,0]); E=R-(DC+DC.T)/2
        vals=[abs(2*normal@G@normal),np.max(abs(normal@G[:,1:])),np.max(abs(C)),np.max(abs(E))]
        maxima=np.maximum(maxima,vals)
    assert np.all(np.isfinite(maxima))
    print('BR246',n,'t',.12-dt,'offset',k*dx,'8 sites max H M C E',maxima.tolist(),flush=True)
    return maxima


def refine():
    a,b,c=[history(n) for n in (11,17,23)]
    print('BR247 fine/coarse ratios H M C E',(c/a).tolist(),flush=True)
    print('BR247 finite diagnostics; sample times and offsets differ, no convergence certificate')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',required=True,choices=['initial','refine']);globals()[{'initial':'initial_weld','refine':'refine'}[p.parse_args().part]]()
