"""BR256: original reduced Ricci donor, fourth-order interior stencils and spatial reconstruction."""
import argparse
import inspect
import numpy as np
from scipy.interpolate import BPoly
from scipy.ndimage import spline_filter,map_coordinates
import check_hopf369_br240_metric_history as d
from check_hopf369_br248_250_forced_subsidiary import probe

def diff(a,dx,axis,edge_order=2):
    b=np.gradient(a,dx,axis=axis,edge_order=edge_order)
    q=np.moveaxis(a,axis,0);r=np.moveaxis(b,axis,0)
    r[2:-2]=(q[:-4]-8*q[1:-3]+8*q[3:-1]-q[4:])/(12*dx)
    return b

def second(a,dx,axis):
    b=(np.roll(a,1,axis=axis)-2*a+np.roll(a,-1,axis=axis))/dx**2
    q=np.moveaxis(a,axis,0);r=np.moveaxis(b,axis,0)
    r[2:-2]=(-q[:-4]+16*q[1:-3]-30*q[2:-2]+16*q[3:-1]-q[4:])/(12*dx**2)
    return b

def operators(order):
    if order==2:return d.initial,d.acceleration
    ns=dict(vars(d),diff=diff,d2=second)
    exec(inspect.getsource(d.spatial).replace('np.gradient','diff'),ns)
    src=inspect.getsource(d.acceleration).replace('np.gradient','diff').replace('(np.roll(g,1,axis=i-1)-2*g+np.roll(g,-1,axis=i-1))/dx**2','d2(g,dx,i-1)')
    assert 'd2(g,dx,i-1)' in src
    exec(src,ns);exec(inspect.getsource(d.jets),ns);exec(inspect.getsource(d.initial),ns)
    return ns['initial'],ns['acceleration']

def run(n,order,steps):
    init,acc=operators(order);g,v,dx=init(n);dt=.12/steps;t=.061;k=int(t/dt);saved=[]
    def rhs(g,v):
        a=acc(g,v,dx);w=v.copy()
        for i in range(3):
            for j in (0,-1):
                p=[slice(None)]*3;p[i]=j;a[tuple(p)]=0;w[tuple(p)]=0
        return w,a
    for j in range(k+2):
        u,a=rhs(g,v)
        if j in (k,k+1):saved.append([g.copy(),u.copy(),a.copy()])
        if j==k+1:break
        w,b=rhs(g+dt*u/2,v+dt*a/2);x,c=rhs(g+dt*w/2,v+dt*b/2);y,e=rhs(g+dt*x,v+dt*c)
        g+=dt*(u+2*w+2*x+y)/6;v+=dt*(a+2*b+2*c+e)/6
        assert np.isfinite(g).all() and np.linalg.eigvalsh(g)[...,0].max()<0 and np.linalg.eigvalsh(g)[...,1].min()>0
    times=np.array([k,k+1])*dt;P=BPoly.from_derivatives(times,saved)
    for i in range(3):assert np.max(abs(P(times,i)-np.array([a[i] for a in saved])))<1e-8
    for degree in (3,5):
        coeff=np.array([[[spline_filter(a[...,i,j],order=degree) for i in range(5) for j in range(5)] for a in row] for row in P.c])
        Q=BPoly(coeff,P.x)
        def read(p):
            q=((p[1:]+1.5)/dx)[:,None]
            return np.array([map_coordinates(c,q,order=degree,prefilter=False)[0] for c in Q(p[0])]).reshape(5,5)
        h=.0002;assert min(t-times[0],times[1]-t)>2*h
        rows=np.array([probe(read,np.array([t,*p]),h) for p in [(0,0,0),(.3,0,0),(.3,-.3,.3)]])
        assert np.isfinite(rows).all()
        print('BR256',n,order,steps,degree,rows[:,:7].max(axis=0).tolist(),'margin',rows[:,7].min(),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,required=True);p.add_argument('--order',type=int,choices=[2,4],required=True);p.add_argument('--steps',type=int,default=16);a=p.parse_args();run(a.n,a.order,a.steps)
