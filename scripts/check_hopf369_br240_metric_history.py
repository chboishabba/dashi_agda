#!/usr/bin/env python3
"""BR240: original P0T radial Hopf data, reduced vacuum harmonic evolution.
Finite central-box diagnostic; frozen outer buffer, not an exterior theorem.
"""
import numpy as np
from scipy.integrate import solve_ivp
import argparse


def initial(n,L=1.5):
    x=np.linspace(-L,L,n); dx=x[1]-x[0]; X,Y,Z=np.meshgrid(x,x,x,indexing='ij'); r=np.sqrt(X*X+Y*Y+Z*Z); D=1+r*r
    eps=.25; a=2*eps*np.stack((2*X*Z-2*Y,2*X+2*Y*Z,1-X*X-Y*Y+Z*Z),axis=-1)/D[...,None]**2
    sol=solve_ivp(lambda r,u:[u[1],-eps**2*64/(12*(1+r*r)**4)*u[0]],(0,64),[0,1],rtol=2e-12,atol=2e-14,dense_output=True)
    u=sol.sol(r.ravel())[0].reshape(r.shape); psi=np.divide(u,r,out=np.ones_like(r),where=r>0)/sol.y[1,-1]
    g=np.zeros(r.shape+(5,5)); g[...,0,0]=-1; g[...,1:4,1:4]=np.eye(3)+a[..., :,None]*a[...,None,:]; g[...,1:4,4]=a; g[...,4,1:4]=a; g[...,4,4]=1; g[...,1:,1:]*=psi[...,None,None]**2
    v=np.zeros_like(g); d=spatial(g,dx); inv=np.linalg.inv(g)
    for i in range(1,5):
        v[...,0,i]=v[...,i,0]=sum(inv[...,j,k]*(d[...,j,k,i]-d[...,i,j,k]/2) for j in range(1,5) for k in range(1,5))
    return g,v,dx


def spatial(g,dx):
    d=np.zeros(g.shape[:-2]+(5,5,5));
    for i in range(1,4): d[...,i,:,:]=np.gradient(g,dx,axis=i-1,edge_order=2)
    return d


def jets(g,v,dx):
    d=spatial(g,dx); d[...,0,:,:]=v; I=np.linalg.inv(g)
    # L_{a b c}=Gamma_{a,bc}; d[...,b,a,c] = partial_b g_ac
    L=(np.swapaxes(d,-3,-2)+np.moveaxis(d,-3,-1)-d)/2
    G=np.einsum('...ae,...ebc->...abc',I,L)
    C=np.einsum('...bc,...abc->...a',I,L)
    return d,I,G,C


def acceleration(g,v,dx):
    d,I,G,C=jets(g,v,dx)
    # Direct lower Ricci minus symmetric covariant derivative of lowered C,
    # holding all second jets zero. Principal term is -1/2 g^ab g_mn,ab.
    di=-np.einsum('...ar,...krs,...sb->...kab',I,d,I)
    L=np.einsum('...ae,...ebc->...abc',g,G)
    dG=np.einsum('...kae,...ebc->...kabc',di,L)
    Q=np.einsum('...aamn->...mn',dG)-np.einsum('...nama->...mn',dG)
    Q+=np.einsum('...aac,...cmn->...mn',G,G)-np.einsum('...anc,...cma->...mn',G,G)
    dC=np.einsum('...kbc,...abc->...ka',di,L)
    Q-=.5*(dC+np.swapaxes(dC,-1,-2))-np.einsum('...amn,...a->...mn',G,C)
    principal=np.zeros_like(g)
    for i in range(1,4):
        principal+=2*I[...,0,i,None,None]*np.gradient(v,dx,axis=i-1,edge_order=2)
        for j in range(1,4):
            if i==j:
                second=(np.roll(g,1,axis=i-1)-2*g+np.roll(g,-1,axis=i-1))/dx**2
            else: second=np.gradient(d[...,j,:,:],dx,axis=i-1,edge_order=2)
            principal+=I[...,i,j,None,None]*second
    a=(2*Q-principal)/I[...,0,0,None,None]
    a=(a+np.swapaxes(a,-1,-2))/2
    return a


def run(n, full=False):
    g,v,dx=initial(n); g0=g.copy(); v0=v.copy(); dt=.12/int(round(.12/(.1*dx))); steps=int(round(.12/dt))
    sl=(slice(3,-3),)*3; center=(n//2,)*3
    def rhs(g,v):
        a=acceleration(g,v,dx); vv=v.copy()
        for i in range(3):
            for k in (0,-1):
                idx=[slice(None)]*3;idx[i]=k; a[tuple(idx)]=0; vv[tuple(idx)]=0
        return vv,a
    c0=np.max(abs(jets(g,v,dx)[3][sl])); assert c0<1e-10
    history=[g.copy() if full else g[center].copy()]
    for k in range(steps):
        u,a=rhs(g,v); w,b=rhs(g+dt*u/2,v+dt*a/2); g+=dt*w;v+=dt*b
        assert np.max(np.linalg.eigvalsh(g)[...,0])<0 and np.min(np.linalg.eigvalsh(g)[...,1])>0
        assert np.all(np.isfinite(g)); history.append(g.copy() if full else g[center].copy())
    common=np.flatnonzero(abs(np.linspace(-1.5,1.5,n))<=.6+1e-12); cc=jets(g,v,dx)[3]; ccommon=np.max(abs(cc[np.ix_(common,common,common)])); c1=np.max(abs(cc[sl])); change=np.max(abs(g[sl]-g0[sl])); assert change>0
    # KK inverse: q=g44, a_i=g_i4/q, horizontal Schur complement.
    H=g[sl]; q=H[...,4,4]; a=H[...,1:4,4]/q[...,None]; h=H[...,1:4,1:4]-q[...,None,None]*a[..., :,None]*a[...,None,:]
    assert np.min(np.linalg.eigvalsh(h))>0
    print('BR240',n,'dt',dt,'gauge initial',c0,'final',c1,'common cube gauge',ccommon,'change',change,'center radius squared',g[center][4,4], 'horizontal volume',np.sqrt(np.linalg.det(h)).min(),flush=True)
    return history,dx

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=11);a=p.parse_args();run(a.n)
