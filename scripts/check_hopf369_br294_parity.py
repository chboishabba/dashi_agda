"""Exact parity kernel and boundary compatibility lift of BR293's linear operator."""
import argparse
import numpy as np
from scipy.sparse import kron,eye,csr_matrix
from scipy.sparse.linalg import lsqr
import check_hopf369_br292_geometry_inverse as base
import check_hopf369_br290_magnetic_curl as magnetic

def run(n):
    g,v,U,dx=magnetic.initial(n); sl=(slice(1,-1),)*3; m=(n-2)**3; N=n**3
    ids=np.arange(N).reshape((n,)*3)[sl].ravel(); outer=np.setdiff1d(np.arange(N),ids)
    _,J,pairs=base.operators(n,dx)
    diag=np.array([i==j for i,j in pairs],int); P=np.eye(6)-np.outer(diag,diag)/3
    W=P@np.diag([1 if i==j else .5 for i,j in pairs])
    Ji=J[:,np.concatenate([ids+i*N for i in range(6)])]
    Jo=J[:,np.concatenate([outer+i*N for i in range(6)])]
    L=-kron(csr_matrix(W),eye(m))@Ji.T; A=Ji@L
    mask=np.zeros((n-2,)*3);mask[::2,::2,::2]=1
    Z=np.kron(np.eye(3),mask.reshape(-1,1)); Z/=np.linalg.norm(Z,axis=0)
    assert np.max(abs(Ji.T@Z))<1e-12
    rank=np.linalg.matrix_rank(A.toarray(),tol=1e-10); assert rank==3*m-3
    # Three tracefree exterior lifts, chosen by the adjoint of the missing modes.
    B=Jo@kron(csr_matrix(W),eye(len(outer)))@Jo.T@Z
    G=Z.T@B; assert np.linalg.matrix_rank(G)==3
    r=base.constraints(g,v,U,dx)[sl]; f=-np.moveaxis(r[...,1:],-1,0).ravel()
    c=np.linalg.solve(G,Z.T@f); q=kron(csr_matrix(W),eye(len(outer)))@Jo.T@Z@c
    compatible=f-Jo@q; w=lsqr(A,compatible,atol=1e-13,btol=1e-13,iter_lim=10000)[0]
    err=np.max(abs(A@w+Jo@q-f)); assert err<1e-9
    assert np.max(abs(diag@q.reshape(6,-1)))<1e-12
    print('BR294',n,'rank',rank,'parity projection',np.max(abs(Z@Z.T@f)),'lift max',np.max(abs(q)),'linear residual',err,'lift Gram',G.tolist(),flush=True)
    # Even interior size has no centered one-dimensional zero mode.
    k=n-1; _,J2,p=base.operators(k,dx); M=(k-2)**3; ids2=np.arange(k**3).reshape((k,)*3)[sl].ravel(); J2=J2[:,np.concatenate([ids2+i*k**3 for i in range(6)])]; A2=J2@kron(csr_matrix(W),eye(M))@J2.T
    rank2=np.linalg.matrix_rank(A2.toarray(),tol=1e-10); assert rank2==3*M
    print('BR294 even interior',k-2,'rank',rank2,'of',3*M,flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=7);run(p.parse_args().n)
