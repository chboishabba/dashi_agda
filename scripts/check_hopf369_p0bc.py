"""BC: normal Taylor development of the original BB timelike wall.
Finite-difference tangential jets, cubic normal polynomial, no global bulk solve.
"""
import numpy as np
from check_hopf369_p0bb import setup, step, kt


def curvature(h, spacing):
    I=np.linalg.inv(h)
    d=lambda a,k:(np.roll(a,-1,k)-np.roll(a,1,k))/(2*spacing[k])
    dh=np.stack([d(h,k) for k in range(4)],-1)
    dd=np.stack([d(dh,k) for k in range(4)],-1)
    for k in range(4):
        dd[...,k,k]=(np.roll(h,-1,k)-2*h+np.roll(h,1,k))/spacing[k]**2
    T=dh.swapaxes(-1,-2)+dh-np.moveaxis(dh,-1,-3)
    G=.5*np.einsum('...al,...lij->...aij',I,T)
    dI=-np.einsum('...ai,...ijk,...jb->...abk',I,dh,I)
    dT=dd.swapaxes(-2,-3)+dd-np.moveaxis(dd,-2,-4)
    dG=.5*(np.einsum('...alk,...lij->...aijk',dI,T)+np.einsum('...al,...lijk->...aijk',I,dT))
    Ric=np.einsum('...aija->...ij',dG)-np.einsum('...aiaj->...ij',dG)+np.einsum('...aab,...bij->...ij',G,G)-np.einsum('...ajb,...bia->...ij',G,G)
    return I,G,Ric,d


def normal_rhs(h,K,spacing):
    I,G,Ric,_=curvature(h,spacing); A=I@K; tau=np.trace(A,axis1=-2,axis2=-1)
    return Ric+4*h-tau[...,None,None]*K+2*K@A


def residual(h,K,D,spacing):
    I,G,Ric,d=curvature(h,spacing); A=I@K; tau=np.trace(A,axis1=-2,axis2=-1)
    Eab=Ric+4*h-D-tau[...,None,None]*K+2*K@A
    Enn=4-np.trace(I@D,axis1=-2,axis2=-1)+np.trace(A@A,axis1=-2,axis2=-1)
    dK=np.stack([d(K,k) for k in range(4)],-1)
    DK=dK-np.einsum('...lki,...lj->...ijk',G,K)-np.einsum('...lkj,...il->...ijk',G,K)
    Ena=np.einsum('...ik,...ijk->...j',I,DK)-np.stack([d(tau,k) for k in range(4)],-1)
    return Eab,Enn,Ena


def wall(eps,dx=.015,dt=.006):
    N=21; Y,f,H,Q=setup(N,eps,dx)
    crop=(slice(N-4,N+5),)*3
    values={0:Y[crop].copy()}; Z=Y
    for k in range(1,5):
        Z=step(Z,f,dt); values[k]=Z[crop].copy()
    for k in range(1,3):values[-k]=values[k]*np.array([1,-1,1,-1,-1,-1])
    Y=np.stack([values[k] for k in range(-2,5)]); H=H[crop]; Q=Q[crop]
    p=Y[...,0]; s=Y[...,2]; B=Y[...,3:]; H=np.exp(2*p)[...,None,None]*H
    h=np.zeros(p.shape+(4,4));h[...,0,0]=-1;h[...,1:,1:]=H
    M=np.zeros_like(h);M[...,0,0]=s;M[...,0,1:]=M[...,1:,0]=B;M[...,1:,1:]=H@(Q+s[...,None,None]*np.eye(3)/3)
    return h,M,(dt,dx,dx,dx)


def run(eps):
    h,M,spacing=wall(eps); core=(3,slice(3,6),slice(3,6),slice(3,6)); ma=lambda a:float(np.max(abs(a[core])))
    print('wall',eps,'mixed',ma(M[...,0,1:]),flush=True)
    J=-kt/3; Ds=[]; Fs=[]
    for side in (1,-1):
        K=M+side*J*h/2; D=normal_rhs(h,K,spacing); Ds.append(D)
        eta=1e-5
        F=(normal_rhs(h+2*eta*K,K+eta*D,spacing)-normal_rhs(h-2*eta*K,K-eta*D,spacing))/(2*eta); Fs.append(F)
        base=residual(h,K,D,spacing); print('side',side,'wall E',*[ma(a) for a in base],flush=True)
        errs=[]
        for r in (.02,.01,.005):
            n=side*r
            H2=h+2*n*K+n*n*D; K2=K+n*D
            H3=H2+n**3*F/3; K3=K2+n*n*F/2
            e2=residual(H2,K2,D,spacing);e3=residual(H3,K3,D+n*F,spacing)
            eig=np.linalg.eigvalsh(H3[core]);assert np.all(eig[...,0]<0) and np.all(eig[...,1:]>0)
            a,b=ma(e2[0]),ma(e3[0]);errs.append(b)
            print('n',n,'quadratic/cubic tangent',a,b,'normal',ma(e3[1]),'mixed',ma(e3[2]),flush=True)
            assert b<a
        assert errs[0]/errs[1]>3 and errs[1]/errs[2]>3
    print('D jump',ma(Ds[0]-Ds[1]),'F jump',ma(Fs[0]-Fs[1]),flush=True)
    assert ma(Ds[0]-Ds[1])<1e-10
    return Ds,Fs


if __name__=='__main__':
    for eps in (.025,-.025,0.):run(eps)
