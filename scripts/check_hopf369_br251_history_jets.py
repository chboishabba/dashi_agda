"""BR251-252: velocity-custodied Hermite metric history versus spline donor."""
import argparse
import numpy as np
from scipy.ndimage import spline_filter, map_coordinates
from scipy.interpolate import CubicHermiteSpline
from check_hopf369_br240_metric_history import initial, acceleration, spatial
from check_hopf369_br248_250_forced_subsidiary import probe

def run(n):
    g,v,dx=initial(n); dt=.06/{11:4,17:6,23:8}[n]; steps=round(.12/dt)
    gs=[g.copy()]; vs=[v.copy()]
    def rhs(g,v):
        a=acceleration(g,v,dx); vv=v.copy()
        for i in range(3):
            for j in (0,-1):
                p=[slice(None)]*3;p[i]=j;a[tuple(p)]=0;vv[tuple(p)]=0
        return vv,a
    for _ in range(steps):
        u,a=rhs(g,v); w,b=rhs(g+dt*u/2,v+dt*a/2);g+=dt*w;v+=dt*b
        gs.append(g.copy());vs.append(v.copy())
    G=np.array(gs); V=np.array(vs); times=np.arange(steps+1)*dt
    H=CubicHermiteSpline(times,G,V,axis=0)
    assert np.max(abs(H(times)-G))<1e-12 and np.max(abs(H(times,1)-V))<1e-12
    def coeff(X):return np.array([[spline_filter(a[...,i,j],order=3) for i in range(5) for j in range(5)] for a in X])
    gc=coeff(G);vc=coeff(V)
    old=[spline_filter(G[...,i,j],order=3) for i in range(5) for j in range(5)]
    def read_old(p):
        q=((p-np.array([0,-1.5,-1.5,-1.5]))/np.array([dt,dx,dx,dx]))[:,None]
        return np.array([map_coordinates(c,q,order=3,prefilter=False)[0] for c in old]).reshape(5,5)
    def read(p):
        t=p[0]; j=min(steps-1,max(0,int(np.floor(t/dt)))); u=(t-times[j])/dt
        q=((p[1:]+1.5)/dx)[:,None]
        c=(2*u**3-3*u*u+1)*gc[j]+(u**3-2*u*u+u)*dt*vc[j]+(-2*u**3+3*u*u)*gc[j+1]+(u**3-u*u)*dt*vc[j+1]
        return np.array([map_coordinates(a,q,order=3,prefilter=False)[0] for a in c]).reshape(5,5)
    m=n//2; p=np.array([.06,0.,0.,0.]); k=round(.06/dt)
    assert np.max(abs(read(p)-G[k,m,m,m]))<1e-12
    D=spatial(G[k],dx)[m,m,m]; eye=np.eye(4)*.001
    discrepancy=max(np.max(abs((read(p+eye[i])-read(p-eye[i]))/.002-D[i])) for i in range(1,4))
    print('BR251',n,'metric/velocity endpoint custody PASS; spatial derivative discrepancy',discrepancy,flush=True)
    pts=np.array([[.061,0,0,0],[.061,.3,0,0],[.061,.3,-.3,.3]])
    for name,fn in [('spline',read_old),('Hermite',read)]:
        for h in (.0004,.0002):
            a=np.array([probe(fn,p,h) for p in pts]);assert np.isfinite(a).all()
            print('BR252',n,name,h,'max [defect,force,E,H,M,C,energy]',a[:,:7].max(axis=0).tolist(),'margin',a[:,7].min(),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,choices=[11,17,23],required=True);run(p.parse_args().n)
