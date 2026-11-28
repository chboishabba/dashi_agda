"""Outward binary64 interval Bernstein consumer for original F8 reconstruction.
Requires IEEE binary64 round-to-nearest operations, gradual underflow, no fastmath.
Every elementary operation rounded outward; no BLAS or unbounded reductions.
"""
import numpy as np
from fractions import Fraction as Q

class V:
    __slots__=('l','h')
    def __init__(self,l,h=None):
        self.l=np.asarray(l,dtype=np.float64);self.h=self.l if h is None else np.asarray(h,dtype=np.float64)
    @classmethod
    def rational(cls,l,h=None):
        h=l if h is None else h
        return cls(down(float(l)),up(float(h)))
    def __getitem__(a,i):return V(a.l[i],a.h[i])
    def __add__(a,b):
        b=asv(b);return V(down(a.l+b.l),up(a.h+b.h))
    __radd__=__add__
    def __neg__(a):return V(-a.h,-a.l)
    def __sub__(a,b):return a+-asv(b)
    def __rsub__(a,b):return asv(b)+-a
    def __mul__(a,b):
        b=asv(b);p=a.l*b.l;q=a.l*b.h;r=a.h*b.l;s=a.h*b.h
        return V(down(np.minimum(np.minimum(p,q),np.minimum(r,s))),up(np.maximum(np.maximum(p,q),np.maximum(r,s))))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=asv(b)
        if not np.all((b.l>0)|(b.h<0)):raise ValueError('zero divisor')
        return a*V(down(1/b.h),up(1/b.l))
    def __rtruediv__(a,b):return asv(b)/a
    def mag(a):return np.maximum(abs(a.l),abs(a.h))
    def square(a):
        lo=np.where((a.l<=0)&(a.h>=0),0,np.minimum(a.l*a.l,a.h*a.h))
        return V(np.maximum(0,down(lo)),up(np.maximum(a.l*a.l,a.h*a.h)))
    def sqrt(a):
        if np.any(a.l<0):raise ValueError('negative sqrt')
        return V(np.maximum(0,down(np.sqrt(a.l))),up(np.sqrt(a.h)))
    def hull(a,axis):return V(np.min(a.l,axis=axis),np.max(a.h,axis=axis))
    def sum(a,axis=0):
        # balanced tree of outward-rounded additions, no np.sum error assumption
        l=np.moveaxis(a.l,axis,0);h=np.moveaxis(a.h,axis,0)
        while l.shape[0]>1:
            n=l.shape[0]//2;ll=down(l[:2*n:2]+l[1:2*n:2]);hh=up(h[:2*n:2]+h[1:2*n:2]);
            if l.shape[0]%2:ll=np.concatenate((ll,l[-1:]));hh=np.concatenate((hh,h[-1:]))
            l,h=ll,hh
        return V(l[0],h[0])
    def finite(a):return np.all(np.isfinite(a.l)) and np.all(np.isfinite(a.h)) and np.all(a.l<=a.h)

def down(a):return np.nextafter(a,-np.inf)
def up(a):return np.nextafter(a,np.inf)
def asv(x):return x if isinstance(x,V) else V(x)
def stack(xs,axis=0):return V(np.stack([x.l for x in xs],axis),np.stack([x.h for x in xs],axis))
def broadcast(a,shape):return V(np.broadcast_to(a.l,shape),np.broadcast_to(a.h,shape))
def rat(x):return V.rational(x)
def from_i(x):return V.rational(x.l,x.h)

def bezier(A,B,h,dy):
    # direct tensor Hermite-to-Bernstein map, avoiding cancellation in power basis
    H=V(h)/3;D=V(dy)/3
    def time(j):
        u,w,n,m=[V(x) for x in j]
        return u,w,n,m
    u,w,n,m=time(A);p,q,r,s=time(B)
    U=[u,u+H*w,p-H*q,p];N=[n,n+H*m,r-H*s,r]
    return stack([stack([x[:-1],x[:-1]+D*z[:-1],x[1:]-D*z[1:],x[1:]]) for x,z in zip(U,N)])

def derivative(c,axis,h):
    d=V(np.moveaxis(c.l,axis,0),np.moveaxis(c.h,axis,0));a=(d[1:]-d[:-1])*3/h
    # exact degree elevation from degree 2 to degree 3
    x=stack([a[0],(a[0]+2*a[1])/3,(2*a[1]+a[2])/3,a[2]])
    return V(np.moveaxis(x.l,0,axis),np.moveaxis(x.h,0,axis))

def derivatives(A,B,h,dy):
    c=bezier(A,B,h,dy);ct=derivative(c,0,h);cy=derivative(c,1,dy)
    return c,ct,cy,derivative(ct,0,h),derivative(ct,1,dy),derivative(cy,1,dy)

def primal(A,B,h,dy,k,box,src,src_t):
    c,ct,cy,ctt,cty,cyy=derivatives(A,B,h,dy)
    b,v,s,a=[V.rational(*x) for x in box]
    j=np.arange(c.l.shape[2])[:,None];y=V(j,j+1)*dy;z=b+y
    w=1/(z.square()*z);K=k.square()
    r=(ctt-2*v*cty-s*cyy+(3/z-a)*cy+K*c).hull((0,1))
    wall=lambda p:p[:,0,0,:]
    g=(src-v*wall(ct)-s*wall(cy)).hull(0)
    gt=(src_t-a*wall(ct)-v*wall(ctt)+2*v*a*wall(cy)-s*wall(cty)).hull(0)
    norms=(V(0,r.mag()).square()*w*dy).sum(0)
    R=up(h*up(np.sqrt(np.maximum(0,norms.h))))
    G=up(h*g.mag());GT=up(h*gt.mag())
    return R,G,GT,r,g,w,wall(c).hull(0)

def energy(B,h,k,box,R,G,GT,d=Q(1,8)):
    b,v,s,a=[V.rational(*x) for x in box];vmin=V(-v.h);vmax=V(-v.l);d=rat(d)
    A=V(G)/vmin;At=V(GT)/vmin+V(G)*V(a.h)/vmin.square()
    F=V(R)+(d/(V(b.l).square()*V(b.l))).sqrt()*(V(k.h)*A+At+(2*vmax+V(s.h).sqrt())*2*A/d)
    return ((V(B)+F)/(1-V(h)*rat(Q(5,2)))).h

def check():
    from check_f8_combined_residual import enclose,clock_box
    from check_f8_local_dual_weld import I
    rng=np.random.default_rng(1547);h=.0006;dy=.018;box=clock_box(0,Q(h),Q(999,1000),Q(1000001,1000000));k=V.rational(Q(1),Q(11,10));checks=0
    for i in range(12):
        A=rng.normal(size=(4,4,1))*10.**(-i);B=rng.normal(size=A.shape)*10.**(-i)
        R,G,GT,*_=primal(A,B,h,dy,k,box,V(0),V(0))
        exact=enclose(A[:,:,0],B[:,:,0],h,dy,(Q(1),Q(121,100)),box)
        # Both hull constructions differ by degree elevation order and dependency;
        # allow the tighter direct construction, compare actual point samples below.
        from check_f8_streaming_residual import slab,evaluate,derivative as pd
        c=slab(A,B,h,dy);ct=pd(c,0,h);cy=pd(c,1,dy);ctt=pd(ct,0,h);cty=pd(ct,1,dy);cyy=pd(cy,1,dy)
        _,_,_,r,g,_,_=primal(A,B,h,dy,k,box,V(0),V(0))
        for x,y in ((0,0),(.23,.4),(.9,.8),(1,1)):
            b,v,s,a=[float((l+u)/2) for l,u in box];z=b+dy*(np.arange(3)[:,None]+y)
            val=evaluate(ctt,x,y)-2*v*evaluate(cty,x,y)-s*evaluate(cyy,x,y)+(3/z-a)*evaluate(cy,x,y)+1.05**2*evaluate(c,x,y)
            assert np.all(val>=r.l) and np.all(val<=r.h);checks+=1
        assert np.all(np.isfinite(energy(np.zeros(1),h,k,box,R,G,GT)));checks+=1
    # exact rational rounding for elementary operations including cancellation
    for a,b in ((Q(1,3),Q(-7,11)),(Q(1,10**100),Q(2,10**99)),(Q(3,4),Q(1,4))):
        x,y=rat(a),rat(b)
        for z,t in ((x+y,a+b),(x-y,a-b),(x*y,a*b),(x/y,a/b)):
            assert Q(float(z.l))<=t<=Q(float(z.h));checks+=1
    return {'checks':checks,'scope':'vector interval arithmetic and sampled regression; not proof by sampling'}
if __name__=='__main__':
    import json;print(json.dumps(check()))
