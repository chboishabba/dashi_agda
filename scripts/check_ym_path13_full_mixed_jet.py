"""Exact Path13 Eq119/120 mixed background jet at identity, CMP98 (1985).
13^4 offsets, 13-link segment, ordered signed-axis paths; group and Lie jets.
Finite selected-bond receipt, not a uniform physical beta certificate.
"""
import numpy as np
from numba import njit
from fractions import Fraction as F
from itertools import product
N=13**4
PAIRS=[[(a,m^a) for a in range(8) if a&m==a] for m in range(8)]

def qm(a,b):
    x,y,z,w=np.moveaxis(a,-1,0); A,B,C,D=np.moveaxis(b,-1,0)
    return np.stack((x*A-y*B-z*C-w*D,x*B+y*A+z*D-w*C,x*C-y*D+z*A+w*B,x*D+y*C-z*B+w*A),axis=-1)
@njit
def mul_int(a,b):
    out=np.zeros(a.shape,dtype=np.int64)
    for k in range(a.shape[0]):
        for m in range(a.shape[1]):
            for i in range(m+1):
                if i&m != i: continue
                j=m^i
                x,y,z,w=a[k,i]; A,B,C,D=b[k,j]
                out[k,m,0]+=x*A-y*B-z*C-w*D
                out[k,m,1]+=x*B+y*A+z*D-w*C
                out[k,m,2]+=x*C-y*D+z*A+w*B
                out[k,m,3]+=x*D+y*C-z*B+w*A
    return out

def mul(a,b):
    if a.dtype==np.int64 and b.dtype==np.int64:
        shape=np.broadcast_shapes(a.shape,b.shape)
        # Conservative overflow guard, including every intermediate product.
        assert 32*int(np.max(np.abs(a)))*int(np.max(np.abs(b))) < 2**63
        return mul_int(np.ascontiguousarray(np.broadcast_to(a,shape)).reshape(-1,shape[-2],4),np.ascontiguousarray(np.broadcast_to(b,shape)).reshape(-1,shape[-2],4)).reshape(shape)
    out=np.zeros(np.broadcast_shapes(a.shape,b.shape),dtype=np.result_type(a,b))
    for m,ps in enumerate(PAIRS[:out.shape[-2]]):
        for i,j in ps:out[...,m,:]+=qm(a[...,i,:],b[...,j,:])
    return out
def conj(a):
    b=a.copy();b[...,1:]*=-1;return b
def one(shape=(),m=8,dtype=np.int64):
    a=np.zeros(shape+(m,4),dtype=dtype);a[...,0,0]=1;return a
def div(a,d):
    assert np.all(a%d==0);return a//d
def expjet(y):
    assert np.all(y[...,0,:]==0)
    p=mul(y,y);return one(y.shape[:-2],y.shape[-2],y.dtype)+y+div(p,2)+div(mul(p,y),6)
def logjet(q):
    u=q.copy();u[...,0]=0;assert np.all(u[...,0,:]==0)
    return u-div(mul(mul(u,u),u),6)
def left_e(q):
    z=mul(q[...,4:,:],conj(q[...,:4,:]));assert np.all(z[...,0]==0);return z
def comm(y,v):return mul(y,v)-mul(v,y)
def adpoly(y,v,a,b):
    x=comm(y,v);return v+a*x+b*comm(y,x)
def atfield(site,axis,k):
    x,y,z,w=np.moveaxis(site,-1,0)
    color=(x+2*y+3*z+w+axis+k)%3
    val=6*((x+3*y+5*z+7*w+2*axis+k)%5-2)
    val=np.where((x+y+z+w+axis+k)%3==0,val,0)
    v=np.zeros(site.shape[:-1]+(4,),dtype=np.int64)
    np.put_along_axis(v,(color+1)[...,None],val[...,None],axis=-1)
    return v
def link(site,axis):
    shape=site.shape[:-1];q=one(shape)
    for m,k in [(4,2),(1,0),(2,1)]:
        f=one(shape);f[...,m,:]=atfield(site,axis,k);q=mul(q,f)
    return q
def walkword(site,offset):
    q=one(site.shape[:-1]);site=site.copy()
    for axis in range(4):
        direction=np.sign(offset[:,axis]);length=np.abs(offset[:,axis])
        for k in range(int(length.max())):
            active=length>k;neg=direction<0
            start=site.copy();start[:,axis]=(start[:,axis]-neg)%13
            u=link(start,axis);u[neg]=conj(u[neg]);u[~active]=one()
            q=mul(q,u);site[:,axis]=(site[:,axis]+direction*active)%13
    return q,site
def coarse(site,axis):
    off=np.zeros_like(site);off[:,axis]=13
    return walkword(site,off)
def avg(a):
    assert N*int(np.max(np.abs(a))) < 2**63
    return np.array([F(int(v),N) for v in a.sum(axis=0).flat],dtype=object).reshape(a.shape[1:])
def cert(axis):
    offsets=np.array(list(product(range(-6,7),repeat=4)),dtype=np.int64)
    start=np.zeros_like(offsets)
    minus,x=walkword(start,offsets);cross,xp=coarse(x,axis)
    center,plusSite=coarse(start[:1],axis)
    assert np.all(plusSite==0)
    plus,xpp=minus,x
    assert np.array_equal(xp,xpp)
    M=mul(minus,cross);P=mul(center,plus)
    rel=mul(M,conj(P));ys=logjet(rel)
    assert np.array_equal(mul(rel,conj(rel)),one((N,)))
    assert np.array_equal(expjet(ys),rel)
    Y=avg(ys);Y2=mul(Y,Y);EY=one(dtype=object)+Y+Y2*F(1,2)+mul(Y2,Y)*F(1,6)
    direct119=left_e(mul(EY,center[0].astype(object)))
    y=ys[:,:4,:];rM=left_e(M);rP=left_e(P)
    xp1=comm(y,rP);xp2=comm(y,xp1)
    sub=rM-rP-xp1-div(xp2,2)
    xx=comm(y,sub);xxx=comm(y,xx)
    point=sub-div(xx,2)+div(xxx,12)
    assert np.array_equal(point,ys[:,4:,:])
    outer=Y[:4,:];rc=left_e(center[0].astype(object))
    compiled119=adpoly(outer,avg(point),F(1,2),F(1,6))+adpoly(outer,rc,F(1),F(1,2))
    assert np.array_equal(direct119,compiled119)
    rminus=left_e(minus);rplus=left_e(plus)
    c=center[:,:4,:];transport=mul(mul(c,rplus),conj(c))
    correction=avg(transport-rminus)
    q=(compiled119+correction)*F(1,13)
    assert np.array_equal(q,(direct119+correction)*F(1,13))
    print('axis',axis,'offsets',N,'Q, DsQ, DtQ, DstQ:',q[:,1:].tolist(),flush=True)
    assert any(q[3,1:])
    return q
if __name__=='__main__':
    for axis in range(4):cert(axis)
    print('PASS 4 selected bonds / 114244 offset projections, exact mixed jets')
