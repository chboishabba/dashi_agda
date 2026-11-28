"""Fixed-space time refinement, RK4 and acceleration-custodied quintic history.
Finite diagnostics, not a subsidiary IBVP or continuum convergence theorem.
"""
import argparse
import numpy as np
from scipy.interpolate import BPoly
from scipy.ndimage import spline_filter, map_coordinates
from check_hopf369_br240_metric_history import initial, acceleration
from check_hopf369_br248_250_forced_subsidiary import probe


def run(n, method, steps):
    g,v,dx=initial(n); dt=.12/steps
    def rhs(g,v):
        a=acceleration(g,v,dx); w=v.copy()
        for i in range(3):
            for j in (0,-1):
                p=[slice(None)]*3;p[i]=j;a[tuple(p)]=0;w[tuple(p)]=0
        return w,a
    def coeff(a):
        return np.array([spline_filter(a[...,i,j],order=3) for i in range(5) for j in range(5)])
    # Use a smooth interior time not at a knot for any tested step size.
    t=.061; k=int(t/dt); saved=[]
    for j in range(k+2):
        u,a=rhs(g,v)
        if j in (k,k+1): saved.append([coeff(g),coeff(u),coeff(a)])
        if j==k+1: break
        w,b=rhs(g+dt*u/2,v+dt*a/2)
        if method=='rk4':
            x,c=rhs(g+dt*w/2,v+dt*b/2); y,d=rhs(g+dt*x,v+dt*c)
            g+=dt*(u+2*w+2*x+y)/6;v+=dt*(a+2*b+2*c+d)/6
        else:
            g+=dt*w;v+=dt*b
        assert np.isfinite(g).all() and np.linalg.eigvalsh(g)[...,0].max()<0 and np.linalg.eigvalsh(g)[...,1].min()>0
    times=np.array([k,k+1])*dt
    pts=np.array([[t,0,0,0],[t,.3,0,0],[t,.3,-.3,.3]])
    for degree, count in ((3,2),(5,3)):
        P=BPoly.from_derivatives(times,[a[:count] for a in saved])
        for i in range(count):
            assert np.max(abs(P(times,i)-np.array([a[i] for a in saved])))<1e-8
        def read(p):
            q=((p[1:]+1.5)/dx)[:,None]
            return np.array([map_coordinates(c,q,order=3,prefilter=False)[0] for c in P(p[0])]).reshape(5,5)
        h=.0002; assert min(t-times[0],times[1]-t)>2*h
        a=np.array([probe(read,p,h) for p in pts]);assert np.isfinite(a).all()
        print('BR253-255',n,method,steps,degree,'dt',dt,'max [defect,force,E,H,M,C,energy]',a[:,:7].max(axis=0).tolist(),'margin',a[:,7].min(),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,choices=[11,17,23],default=11);p.add_argument('--method',choices=['midpoint','rk4'],required=True);p.add_argument('--steps',type=int,choices=[8,16,32],required=True);a=p.parse_args();run(a.n,a.method,a.steps)
