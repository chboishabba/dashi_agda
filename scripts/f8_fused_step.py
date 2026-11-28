"""Full six-channel weighted4 RK3 fusion; original stage is reference."""
import numpy as np
from numba import njit, prange

def weights(b,dy,ny):
    z=b+dy*np.arange(ny);H=np.ones(ny);H[[0,-1]]=.5;B=H*z**-3
    lo=np.zeros(ny);hi=lo.copy();al=lo.copy();ah=lo.copy()
    for i in range(ny):
        if i:lo[i]=(-1. if i==ny-1 else -.5)*np.expm1(-1.5*np.log1p((z[i-1]-z[i])/z[i]))/dy
        if i<ny-1:hi[i]=(1. if i==0 else .5)*np.expm1(-1.5*np.log1p((z[i+1]-z[i])/z[i]))/dy
    for i in range(ny):
        if i:al[i]=hi[i-1]*B[i-1]/B[i]
        if i<ny-1:ah[i]=lo[i+1]*B[i+1]/B[i]
    return z,lo,hi,al,ah

@njit(inline='always')
def combine(x,base,r,h,k):
    u=x+h*r
    if k==0:return u
    if k==1:return .75*base+.25*u
    return (base+2*u)/3

@njit(cache=True,parallel=True)
def stage(X,base,out,h,k,dr,dy,b,v,amp,src,cp,cm,paired,z,lo,hi,al,ah):
    _,nm,ny,nr=X.shape;dr2=dr*dr
    for line in prange(nm*ny):
        q=line//ny;i=line%ny;d=3+4*q;zi=b+i*dy
        wl=(zi/(zi-dy))**1.5 if i else 0.
        wh=(zi/(zi+dy))**1.5 if i<ny-1 else 0.
        for j in range(nr-1):
            u=X[0,q,i,j];p=X[1,q,i,j];m=X[2,q,i,j]
            w=((1+v)*p+(1-v)*m)/2;n=(p-m)/2
            if j==0:radial=2*d*(X[0,q,i,1]-u)/dr2
            else:radial=(cp[q,j]*(X[0,q,i,j+1]-u)-cm[q,j]*(u-X[0,q,i,j-1]))/dr2
            force=radial-3*n/zi
            cw=1.5*w/z[i];cn=1.5*n/z[i]
            if i:
                pl=X[1,q,i-1,j];ml=X[2,q,i-1,j]
                cw+=lo[i]*(((1+v)*pl+(1-v)*ml)/2);cn+=al[i]*((pl-ml)/2)
            if i<ny-1:
                ph=X[1,q,i+1,j];mh=X[2,q,i+1,j]
                cw+=hi[i]*(((1+v)*ph+(1-v)*mh)/2);cn+=ah[i]*((ph-mh)/2)
            if i==0:
                dp=(wh*ph-p)/dy+1.5*p/zi;dm=(wh*mh-m)/dy+1.5*m/zi
            elif i==ny-1:
                dp=(p-wl*pl)/dy+1.5*p/zi;dm=(m-wl*ml)/dy+1.5*m/zi
            else:
                dp=(wh*ph-wl*pl)/(2*dy)+1.5*p/zi;dm=(wh*mh-wl*ml)/(2*dy)+1.5*m/zi
            rp=(1+v)*dp+force;rm=(v-1)*dm+force;rR=0.;rJ=0.;rK=0.
            if i==ny-1:rp-=2*(1+v)*p/dy;rK=-(1+v)*p/dy
            if i==0:
                target=(2*amp*src[q,j]-(1+v)*p)/(v-1)
                rm+=2*(1-v)*(target-m)/dy
                rJ=-2*(((1+v)*p+(v-1)*m)/2-amp*src[q,j])/dy
            if paired:
                dw=(1-v*v)*cn;dn=-cw
                rp+=dw+(1-v)*dn;rm+=dw-(1+v)*dn
            else:rR=cw
            out[0,q,i,j]=combine(u,base[0,q,i,j],w,h,k)
            out[1,q,i,j]=combine(p,base[1,q,i,j],rp,h,k)
            out[2,q,i,j]=combine(m,base[2,q,i,j],rm,h,k)
            out[3,q,i,j]=combine(X[3,q,i,j],base[3,q,i,j],rR,h,k)
            out[4,q,i,j]=combine(X[4,q,i,j],base[4,q,i,j],rJ,h,k)
            out[5,q,i,j]=combine(X[5,q,i,j],base[5,q,i,j],rK,h,k)
        for c in range(6):out[c,q,i,nr-1]=0.

def step_into(X,out,a,b,T,h,coeff,dr,dy,src,cp,cm,route):
    if route not in ('ledger','paired'):raise ValueError('explicit route')
    if any(np.may_share_memory(x,y) for i,x in enumerate((X,out,a,b)) for y in (X,out,a,b)[i+1:]):raise ValueError('distinct buffers required')
    for k,(inp,dst,t) in enumerate(((X,a,T),(a,b,T+h),(b,out,T+h/2))):
        v,z,amp=coeff(t)
        stage(inp,X,dst,h,k,dr,dy,z,v,amp,src,cp,cm,route=='paired',*weights(z,dy,X.shape[-2]))
    return out
