"""Fixed outer g,K and densitized U; discrete CMC longitudinal adjoint comparator.
Retain linear cokernel and nonlinear residual; not continuum York BVP.
"""
import argparse
import numpy as np
from scipy.sparse import block_diag, eye, kron, csr_matrix
from scipy.sparse.linalg import lsqr
import check_hopf369_br292_geometry_inverse as base
import check_hopf369_br290_magnetic_curl as magnetic


def run(n):
    g0,v0,U,dx=magnetic.initial(n); U0=U.copy(); K0=-v0[...,1:,1:]/2
    sl=(slice(1,-1),)*3; ids=np.arange(n**3).reshape((n,)*3)[sl].ravel(); m=len(ids)
    lap,J,pairs=base.operators(n,dx); lap=lap[:,ids]; J=J[:,np.concatenate([ids+i*n**3 for i in range(6)])]
    # Symmetric Frobenius projection to trace-free tensors and adjoint York image.
    diag=np.array([int(i==j) for i,j in pairs]); weights=np.array([1 if i==j else 2 for i,j in pairs]);
    P=np.eye(6)-np.outer(diag,diag)/3
    L=-kron(csr_matrix(P@np.diag(1/weights)),eye(m))@J.T
    A=J@L
    rank=np.linalg.matrix_rank(A.toarray(),tol=1e-10)
    tau=np.trace(np.linalg.solve(g0[...,1:,1:],K0),axis1=-2,axis2=-1)
    psi0=g0[...,1,1]**.25; Y0=(K0-tau[...,None,None]*g0[...,1:,1:]/3)*psi0[...,None,None]**2
    u=np.zeros(m); w=np.zeros(3*m)
    def state(u,w):
        psi=psi0.copy();psi[sl]+=u.reshape((n-2,)*3);Y=Y0.copy(); q=(L@w).reshape((6,n-2,n-2,n-2))
        for k,(i,j) in enumerate(pairs):
            Y[sl][...,i,j]+=q[k]
            if i!=j:Y[sl][...,j,i]+=q[k]
        g=g0.copy();g[sl][...,1:,1:]=psi[sl][...,None,None]**4*np.eye(3)
        K=K0.copy();K[sl]=Y[sl]/psi[sl][...,None,None]**2+tau[sl][...,None,None]*g[sl][...,1:,1:]/3
        v=base.jets(g,K,dx);r=base.constraints(g,v,U,dx)[sl];return g,K,v,r
    g,K,v,r=state(u,w); start=np.max(abs(r)); initial=r.copy()
    for k in range(16):
        err=np.max(abs(r)); print('BR293 iteration',k,err,flush=True)
        du=lsqr(4*lap,r[...,0].ravel(),atol=1e-13,btol=1e-13)[0]
        rhs=-np.moveaxis(r[...,1:],-1,0).ravel();dw=lsqr(A,rhs,atol=1e-13,btol=1e-13)[0]
        cok=np.max(abs(A@dw-rhs));
        if k==0:print('BR293 York rank',rank,'of',3*m,'linear unmatched',cok,flush=True)
        accepted=False
        for a in (1.,.5,.25,.125,.0625):
            gg,KK,vv,rr=state(u+a*du,w+a*dw)
            if np.linalg.norm(rr)<np.linalg.norm(r):
                u+=a*du;w+=a*dw;g,K,v,r=gg,KK,vv,rr;accepted=True;break
        if not accepted or np.max(abs(r))<1e-10:break
    mask=np.ones(g.shape[:3],bool);mask[sl]=False
    cmc=np.max(abs(np.trace(np.linalg.solve(g[...,1:,1:],K),axis1=-2,axis2=-1)-tau))
    assert np.array_equal(g[mask],g0[mask]) and np.array_equal(K[mask],K0[mask]) and np.array_equal(U,U0) and cmc<1e-12
    values,b=base.audit.audit(g,v,U,dx);_,_,_,_,margin=base.d.matter(g,U)
    print('BR293 final',n,'initial/final max',start,np.max(abs(r)),'H/M',np.max(abs(r[...,0])),np.max(abs(r[...,1:])),'sample audit',values.tolist(),'CMC',cmc,'margin',margin,'Bdiv',b,'boundary fixed',True,flush=True)
    assert np.linalg.norm(r)<=np.linalg.norm(initial) and margin>0

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=7);run(p.parse_args().n)
