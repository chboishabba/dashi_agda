"""Fixed densitized matter, reverse finite metric/CMC geometry. Central box only."""
import argparse
import numpy as np
from scipy.sparse import coo_matrix, hstack, vstack
from scipy.sparse.linalg import lsqr
import check_hopf369_br283_284_g4_coupled as d
import check_hopf369_br287_289_g4_audit as audit
import check_hopf369_br290_magnetic_curl as magnetic

def jets(g,K,dx):
    v=np.zeros_like(g);v[...,1:,1:]=-2*K
    I=np.linalg.inv(g);f=d.spatial(g,dx)
    v[...,0,0]=-np.einsum('...ij,...ij->...',I[...,1:,1:],v[...,1:,1:])
    v[...,0,1:]=v[...,1:,0]=np.einsum('...jk,...jki->...i',I[...,1:,1:],f[...,1:,1:,1:])-.5*np.einsum('...jk,...ijk->...i',I[...,1:,1:],f[...,1:,1:,1:])
    return v

def constraints(g,v,U,dx):
    I=np.linalg.inv(g); f=np.stack([v,*[audit.diff(g,i,dx) for i in range(3)]],axis=-3)
    s=np.zeros(g.shape[:-2]+(4,4,4,4))
    for i in range(3):
        s[...,0,i+1,:,:]=s[...,i+1,0,:,:]=audit.diff(v,i,dx)
        s[...,i+1,i+1,:,:]=(np.roll(g,-1,axis=i)-2*g+np.roll(g,1,axis=i))/dx**2
        for j in range(i):s[...,i+1,j+1,:,:]=s[...,j+1,i+1,:,:]=audit.diff(audit.diff(g,i,dx),j,dx)
    L=(f.swapaxes(-3,-2)+np.moveaxis(f,-3,-1)-f)/2
    dl=(s.swapaxes(-3,-2)+np.moveaxis(s,-3,-1)-s)/2
    di=-np.einsum('...ar,...krs,...sb->...kab',I,f,I)
    G=np.einsum('...ae,...ebc->...abc',I,L)
    DG=np.einsum('...kae,...ebc->...kabc',di,L)+np.einsum('...ae,...kebc->...kabc',I,dl)
    R=np.einsum('...aamn->...mn',DG)-np.einsum('...nama->...mn',DG)+np.einsum('...aac,...cmn->...mn',G,G)-np.einsum('...anc,...cma->...mn',G,G)
    E=R-.5*g*np.sum(I*R,axis=(-2,-1))[...,None,None]
    root=np.sqrt(np.linalg.det(g[...,1:,1:]));rho=-U[...,0]/root;j=U[...,1:4]/root[...,None]
    return np.concatenate(((E[...,0,0]-d.src.KAP*rho)[...,None],-E[...,0,1:]-d.src.KAP*j),axis=-1)

def operators(n,dx):
    # Unknowns on full grid, constraints on interior. Boundary correction
    # permitted: this is not a fixed physical boundary value problem.
    pts=list(np.ndindex((n-2,)*3));pts=[tuple(k+1 for k in p) for p in pts];N=n**3
    def mat(axis,second=False):
        rows=[];cols=[];vals=[]
        for i,p in enumerate(pts):
            for off,w in ([(-1,1),(0,-2),(1,1)] if second else [(-1,-.5),(1,.5)]):
                q=list(p);q[axis]+=off;rows.append(i);cols.append(np.ravel_multi_index(q,(n,)*3));vals.append(w/dx**(2 if second else 1))
        return coo_matrix((vals,(rows,cols)),shape=(len(pts),N)).tocsr()
    D=[mat(i) for i in range(3)];lap=sum(mat(i,True) for i in range(3));Z=D[0]*0
    # Gnn linear response to h=(1+u)I is -lap u.
    # j=div K-grad tr K. Six symmetric entries ordered below.
    pairs=[(i,j) for i in range(3) for j in range(i,3)]
    blocks=[]
    for i in range(3):
        row=[]
        for a,b in pairs:
            if a==b:row.append(Z if i==a else -D[i])
            else:row.append(D[b] if i==a else D[a] if i==b else Z)
        blocks.append(hstack(row))
    return lap,vstack(blocks).tocsr(),pairs

def initial(n):
    g,v,U,dx=magnetic.initial(n);original=U.copy();g0=g.copy();K=-v[...,1:,1:]/2;K0=K.copy();sl=(slice(1,-1),)*3;lap,J,pairs=operators(n,dx)
    for k in range(16):
        v=jets(g,K,dx);r=constraints(g,v,U,dx)[sl];err=np.max(abs(r));print('BR292 iteration',k,err,flush=True)
        if err<1e-10:break
        du=lsqr(lap,r[...,0].ravel(),atol=1e-13,btol=1e-13)[0].reshape((n,)*3)
        dk=lsqr(J,-np.moveaxis(r[...,1:],-1,0).ravel(),atol=1e-13,btol=1e-13)[0].reshape((6,n,n,n))
        for i in range(3):g[...,i+1,i+1]+=du
        for z,(i,j) in enumerate(pairs):
            K[...,i,j]+=dk[z]
            if i!=j:K[...,j,i]+=dk[z]
    assert err<1e-8 and np.array_equal(U,original)
    values,b=audit.audit(g,v,U,dx);assert max(values[:2])<2e-8 and b<1e-12
    print('BR292 fixed U exact',np.array_equal(U,original),'geometry delta',np.max(abs(g-g0)),np.max(abs(K-K0)),'independent H/M',values[:2],flush=True)
    return g,v,U,dx

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=7);p.add_argument('--steps',type=int,default=2);p.add_argument('--dt',type=float,default=.002);a=p.parse_args();d.initial=initial;audit.run(a.n,a.steps,a.dt)
