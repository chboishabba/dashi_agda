"""Sparse local patch for original six receiver rows; no dense time bank."""
import numpy as np
from check_f8_shrinking_jet import patch,covector,direct
from warp_native_geometric_receiver import rows


def local_slice(x,lo,hi):
    ids=np.flatnonzero((x>lo)&(x<hi))
    if not len(ids) or ids[0]<2 or ids[-1]+2>=len(x):raise ValueError('unresolved padded patch')
    return slice(int(ids[0])-2,int(ids[-1])+3)


def build(T,t,dy,ny,dr,nr,rx,delta,eps=.04):
    T=np.asarray(T);t=np.asarray(t);star=T[-2];ht=T[1]-T[0]
    if len(t)!=len(T) or not np.allclose(np.diff(T),ht) or min(delta,ht,dy,dr)<=0:raise ValueError('patch clock')
    if delta<4*max(ht,dy,dr):raise ValueError('patch underresolved')
    y=np.arange(ny)*dy;r=np.arange(nr-1)*dr
    ts=local_slice(T,star-1.5*delta,star-.5*delta)
    ys=local_slice(y,delta,2*delta);rs=local_slice(r,rx-.5*delta,rx+.5*delta)
    w=patch(T[ts],y[ys],r[rs],star,rx,delta)
    c=np.array([rows(z) for z in t[ts]])
    o=np.array([[covector(c[:,ch],w,r[rs],eps,ell,(ht,dy,dr)) for ell in (0,2,4)] for ch in range(6)])
    return ts,ys,rs,o


def read(p,ch,n,X):
    ts,ys,rs,o=p
    if not ts.start<=n<ts.stop:return np.zeros(3)
    return np.sum(o[ch,:,n-ts.start]*X[0,:,ys,rs],axis=(1,2))


def inject(p,ch,n,X):
    ts,ys,rs,o=p
    out=np.zeros_like(X)
    if ts.start<=n<ts.stop:out[0,:,ys,rs]=o[ch,:,n-ts.start]
    return out


def check():
    from scipy.optimize import brentq
    from check_f8_modal_cfl import clock
    rng=np.random.default_rng(1547);worst=0.;count=0
    for dr,dy in ((.008,.012),(.006,.009)):
        span=clock(12)-clock(1);nt=int(np.ceil(span/.0006));ht=span/nt
        T=np.arange(nt+2)*ht;t=np.array([brentq(lambda z:clock(z)-clock(1)-s,.5,14) for s in T]);rx=2.649365760962
        nr=int(np.ceil(3.01/dr))+1;ny=int(np.ceil(2.016/dy))+1
        for delta in (.06,.09):
            p=build(T,t,dy,ny,dr,nr,rx,delta);ts,ys,rs,o=p
            y=np.arange(ny)*dy;r=np.arange(nr-1)*dr;w=patch(T[ts],y[ys],r[rs],T[-2],rx,delta)
            c=np.array([rows(z) for z in t[ts]]);u=rng.normal(size=o.shape[1:])
            # u shape mode,time,y,r.  Independent original jet contractions.
            for ch in range(6):
                for q,ell in enumerate((0,2,4)):
                    v,b=direct(u[q],c[:,ch],w,r[rs],.04,ell,(ht,dy,dr))
                    a=np.sum(o[ch,q]*u[q]);e=abs(a-v)/max(b,1e-300);assert e<1e-12
                    worst=max(worst,e);count+=1
            X=np.zeros((6,3,ny,nr));n=(ts.start+ts.stop)//2;X[0,:,ys,rs]=u[:,n-ts.start]
            for ch in range(6):
                np.testing.assert_allclose(read(p,ch,n,X),np.sum(inject(p,ch,n,X)*X,axis=(0,2,3)),rtol=1e-12,atol=1e-9)
            assert not np.any(inject(p,0,nt+1,X))
    return dict(checks=count,max_scaled_error=worst)


if __name__=='__main__':print(check())
