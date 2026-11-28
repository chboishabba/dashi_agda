#!/usr/bin/env python3
"""BR241: same-state spatial material comparator from BR240 evolved metric.
Fixed circle-coordinate slice (P0AG chart), normal-observer storage; no shift/lapse
Maxwell or matter backreaction claim. Reservoirs and conductance synthetic.
"""
from itertools import product
import numpy as np
from scipy.interpolate import RegularGridInterpolator
from scipy.optimize import root
from numpy.polynomial.legendre import leggauss
import check_hopf369_p0ag as donor
from check_hopf369_br240_metric_history import run


def assembly(g,order=3):
    z=donor.z; n=g.shape[0]; grid=np.linspace(-1.5,1.5,n)
    sample=RegularGridInterpolator((grid,)*3,g[...,1:4,1:4],bounds_error=True)
    M=np.zeros((54,54)); N=np.zeros((36,36)); V=np.zeros(33)
    t,w=leggauss(order); t=(t+1)/2; w=w/2
    for p in z.cells:
        for ijk in product(range(order),repeat=3):
            x=t[list(ijk)]; e,b=z.basis(p,x); h=sample(np.array(p)+x-1)[0]; d=np.sqrt(np.linalg.det(h)); weight=np.prod(w[list(ijk)])
            assert np.linalg.eigvalsh(h)[0]>0
            M+=weight*e.T@(d*np.linalg.inv(h))@e; N+=weight*b.T@(h/d)@b
    bounds=[(-1,-.5),(-.5,.5),(.5,1)]
    for i,p in enumerate(z.P):
        lo=np.array([bounds[k][0] for k in p]); width=np.array([bounds[k][1]-bounds[k][0] for k in p])
        for ijk in product(range(order),repeat=3):
            h=sample(lo+width*t[list(ijk)])[0]; V[i]+=np.prod(w[list(ijk)]*width)*np.sqrt(np.linalg.det(h))
    V[27:]=4
    H=np.block([[np.linalg.inv(M),np.zeros((54,36))],[np.zeros((36,54)),N]])
    assert np.linalg.eigvalsh(H)[0]>0 and V.min()>0
    return H,V


def material(n=11):
    z=donor.z; B,R=donor.surface(); history,dx=run(n,full=True); dt=.12/(len(history)-1)
    S=np.block([[np.zeros((54,54)),z.C.T],[-z.C,np.zeros((36,36))]]); L=np.vstack((z.J,np.zeros((36,108)))); charges=np.array([1.,-1.])
    H,V=assembly(history[0]); Hstart=H.copy(); Vstart=V.copy()
    n0=np.ones((33,2))*V[:,None]; x=np.r_[np.zeros(54),z.C@np.sin(np.arange(54))*.1]; surf=np.zeros(54); inv=n0.sum(axis=0)
    energy=lambda a,x,H,V:np.sum(a*(np.log(a/V[:,None])-1))+.5*x@H@x
    worst=0.; hwtotal=0.; vwtotal=0.
    for g in history[1:]:
        H1,V1=assembly(g); K=(H+H1)/2; A=np.eye(90)-dt/2*S@K; free=np.linalg.solve(A,x); W=np.linalg.solve(A,dt/2*L)
        def terms(u):
            nn=np.exp(u[:n0.size].reshape(n0.shape)); v=u[n0.size:]; c=nn/V1[:,None]; xi=v[:,None]*charges
            a=c[z.left]*z.bern(-xi); b=c[z.right]*z.bern(xi); m=.1*(a-b); i=m@charges; mid=free-W@i
            return nn,v,a,b,m,i,mid
        def residual(u):
            nn,v,a,b,m,i,mid=terms(u); return np.r_[(nn-n0-dt*z.Vhat@m).ravel(),v-L.T@K@mid]
        sol=root(residual,np.r_[np.log(n0).ravel(),L.T@K@free],options={'xtol':1e-10}); nn,v,a,b,m,i,mid=terms(sol.x); xn=2*mid-x; sn=surf+dt*R@i
        assert np.all(np.isfinite(sol.x)) and min(nn.min(),a.min(),b.min())>0
        diss=dt*np.sum(m*(np.log(a)-np.log(b))); rem=np.sum(n0*np.log(n0/nn)-n0+nn)
        hw=(xn@(H1-H)@xn+x@(H1-H)@x)/4; vw=-np.sum(n0*np.log(V1/V)[:,None])
        err=abs(energy(nn,xn,H1,V1)-energy(n0,x,H,V)-hw-vw+diss+rem)
        gauss=np.max(abs(-z.G@xn[:54]-z.Q@(nn[:27]@charges)-B@sn))
        worst=max(worst,err,gauss,np.max(abs(z.Z@xn[54:])),np.max(abs(residual(sol.x))),np.max(abs(nn.sum(axis=0)-inv)),abs(sn.sum()-(nn[27:]@charges).sum()))
        assert min(diss,rem)>=-1e-10 and worst<1e-8
        n0,x,surf,H,V=nn,xn,sn,H1,V1; hwtotal+=hw; vwtotal+=vw
    dh=np.linalg.norm(H-Hstart); dv=np.linalg.norm(V-Vstart); assert min(dh,dv)>1e-8
    print('BR241',n,'steps',len(history)-1,'max residual',worst,'Hodge change',dh,'volume change',dv,'Hodge work',hwtotal,'volume work',vwtotal,flush=True)

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser(); p.add_argument('--n',type=int,default=11); material(p.parse_args().n)
