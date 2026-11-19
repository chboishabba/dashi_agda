"""Cached temporal stencil and reusable, batched SSPRK3 driver.
State layout (batch, field, mode, normal, radial); outer radial projection.
"""
import numpy as np
from numba import njit, prange
from scipy.optimize import brentq
from math import asinh, sqrt


def coefficients(times, ny, dy, order):
    F = lambda t: asinh(t)-sqrt(1+t*t)/t
    ts = np.array([brentq(lambda t:F(t)-F(1)-s,.5,100.) for s in times])
    v = -1/np.sqrt(1+ts*ts)
    z = 1/ts[:,None]+dy*np.arange(ny)[None,:]
    D = np.zeros((len(times),ny,3))
    D[:,0,1:] = np.array([-1,1])/dy
    D[:,-1,:2] = np.array([-1,1])/dy
    D[:,1:-1,0] = -.5/dy
    D[:,1:-1,2] = .5/dy
    if order == 4:
        D[:,1:,0] *= (z[:,1:]/z[:,:-1])**1.5
        D[:,:-1,2] *= (z[:,:-1]/z[:,1:])**1.5
        D[:,:,1] += 1.5/z
    DT = np.zeros_like(D)
    DT[:,:,1] = D[:,:,1]
    DT[:,1:,0] = D[:,:-1,2]
    DT[:,:-1,2] = D[:,1:,0]
    return ts,v,1/ts,1.5/z,D,DT


def radial_bands(nr,dr):
    R=np.zeros((3,nr,3))
    for q in range(3):
        d=3+4*q
        R[q,0,1:]=[-2*d,2*d]
        j=np.arange(1,nr-1); den=(j+.5)**d-(j-.5)**d
        p=d*(j+.5)**(d-1)/den; m=d*(j-.5)**(d-1)/den
        R[q,1:-1,0]=m; R[q,1:-1,1]=-p-m; R[q,1:-1,2]=p
    R/=dr**2
    RT=np.zeros_like(R);RT[:,:,1]=R[:,:,1];RT[:,1:,0]=R[:,:-1,2];RT[:,:-1,2]=R[:,1:,0]
    return R,RT

@njit(cache=True,parallel=True)
def stage_into(x,out,R,D,v,Z,dy,h,source,amp,adj):
    nb,_,nm,ny,nr=x.shape
    a=1+v;c=1-v
    for index in prange(nb*nm*ny):
        i=index%ny;q=(index//ny)%nm; l=index//(ny*nm)
        for j in range(nr-1):
            u,p,m=x[l,0,q,i,j],x[l,1,q,i,j],x[l,2,q,i,j]
            r=0.;dp=0.;dm=0.
            for k in range(3):
                jj=j+k-1;ii=i+k-1
                if 0<=jj<nr-1:
                    rv=x[l,0,q,i,jj] if not adj else x[l,1,q,i,jj]+x[l,2,q,i,jj]
                    r+=R[q,j,k]*rv
                if 0<=ii<ny:
                    dp+=D[i,k]*x[l,1,q,ii,j]
                    dm+=D[i,k]*x[l,2,q,ii,j]
            if adj:
                du=r; dp=a*u/2+a*dp-Z[i]*(p+m);dm=c*u/2-c*dm+Z[i]*(p+m)
                if i==ny-1:dp-=2*a*p/dy
                if i==0:dp+=2*a*m/dy;dm-=2*c*m/dy
            else:
                du=(a*p+c*m)/2; f=r-Z[i]*(p-m)
                dp=a*dp+f;dm=-c*dm+f
                if i==ny-1:dp-=2*a*p/dy
                if i==0:dm+=2*(a*p-c*m-2*amp[l]*source[q,j])/dy
            out[l,0,q,i,j]=u+h*du;out[l,1,q,i,j]=p+h*dp;out[l,2,q,i,j]=m+h*dm
        out[l,:,q,i,-1]=0

@njit(cache=True,parallel=True)
def combine(out,x,y,a,b):
    A=out.reshape(-1); X=x.reshape(-1); Y=y.reshape(-1)
    for i in prange(len(A)):A[i]=a*X[i]+b*Y[i]


def propagate(controls, observations, h, dy, R, RT, coeff, source, adj=False):
    """Observations shape (channels,3,3,modes,ny,nr), final three time nodes."""
    ts,v,b,Z,D,DT=coeff; nt=(len(ts)-3)//2
    nb=observations.shape[0] if adj else controls.shape[0]
    shape=(nb,)+observations.shape[2:]
    x=np.zeros(shape); s1=np.empty_like(x); s2=np.empty_like(x); tmp=np.empty_like(x)
    zero=np.zeros(nb); result=np.zeros((nb,len(ts))) if adj else np.zeros((nb,observations.shape[0]))
    J=-4*h*source/dy;J=J.copy();J[:,-1]=0
    if adj:x[:]=observations[:,2]
    def B(z,out,k,amp):
        stage_into(z,out,RT if adj else R,DT[k] if adj else D[k],v[k],Z[k],dy,h,source,amp,adj)
    for n in (range(nt,-1,-1) if adj else range(nt+2)):
        k=2*n
        if adj:
            B(x,s2,k+1,zero);combine(s2,s2,s2,2/3,0.)
            B(s2,s1,k+2,zero);combine(s1,s1,s1,.25,0.)
            result[:,k+1]+=2/3*np.einsum('bqr,qr->b',x[:,2,:,0,:],J)
            result[:,k+2]+=.25*np.einsum('bqr,qr->b',s2[:,2,:,0,:],J)
            result[:,k]+=np.einsum('bqr,qr->b',s1[:,2,:,0,:],J)
            B(s1,tmp,k,zero);combine(x,x,s2,1/3,.75);combine(x,x,tmp,1.,1.)
            if n>=nt-1:x+=observations[:,n-(nt-1)]
        else:
            if n>=nt-1:
                result+=x.reshape(nb,-1)@observations[:,n-(nt-1)].reshape(observations.shape[0],-1).T
            if n==nt+1:break
            B(x,s1,k,controls[:,k]);B(s1,tmp,k+2,controls[:,k+2]);combine(s2,x,tmp,.75,.25)
            B(s2,tmp,k+1,controls[:,k+1]);combine(x,x,tmp,1/3,2/3)
    return result
