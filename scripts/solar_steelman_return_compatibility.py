"""Forced neutral compatibility and sufficient contraction tests.
Numerical return diagnostics, not interval certification.
"""
import numpy as np
from scipy.linalg import schur,svdvals

def audit(M,eps=1e-7,powers=8):
    # Complex Schur ordering separates strictly contracting from centre and
    # unstable eigenvalues without assuming an orthogonal eigenbasis.
    M=np.asarray(M);d=len(M)
    T,U,k=schur(M,output='complex',sort=lambda x:abs(x)<1-eps)
    stable=T[:k,:k];coupling=T[:k,k:];centre=T[k:,k:]
    vals=np.diag(centre)
    P=np.eye(k,dtype=complex);bound=None
    for j in range(1,powers+1):
        P=stable@P
        norm=np.linalg.norm(P,2) if k else 0.
        if norm<1:bound=(j,float(norm));break
    chains=[]
    for v in vals:
        if abs(abs(v)-1)>eps:continue
        N=M-v*np.eye(d);N2=N@N
        chains.append((complex(v),int(sum(svdvals(N)<eps)),int(sum(svdvals(N2)<eps))))
    # Exact range equation for a fixed neutral forcing column is
    # (I-M)x=b. SVD gives numerical residual and null witnesses.
    print('contracting dimension',k,'centre/unstable',d-k,'power bound',bound,flush=True)
    print('unit Jordan diagnostics',chains,flush=True)
    return dict(stable=stable,centre=centre,coupling=coupling,unit=chains,power_bound=bound,
                unstable=int(sum(abs(vals)>1+eps)))

def forced_compatibility(M,b,eps=1e-7):
    L=np.eye(len(M))-M
    x,_,rank,_=np.linalg.lstsq(L,b,rcond=eps)
    r=b-L@x
    return dict(rank=int(rank),residual=float(np.linalg.norm(r)),relative=float(np.linalg.norm(r)/max(1.,np.linalg.norm(b))),
                dual_residual=float(np.linalg.norm(L.conj().T@r)))

def run(M):
    for eps in (1e-5,1e-7,1e-9):
        r=audit(M,eps)
        print('threshold',eps,'unstable',r['unstable'])
    print('LIMIT exact invariant leaves, full Jordan classification and interval margins remain independent')

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('matrix');a=p.parse_args()
    with np.load(a.matrix,allow_pickle=False) as f:run(f['M'])
