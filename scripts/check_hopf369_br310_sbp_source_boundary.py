"""BR310: original BR283 conservative source and first-order SBP boundary ABI.
The original BR302 edge_order=2 derivative is NOT SBP; this script records
that obstruction and constructs a diagonal-norm 3D SBP alternative.
No characteristic SAT/physical exterior or stable nonlinear theorem.
"""
import argparse
import numpy as np
import check_hopf369_br283_284_g4_coupled as d

def sbp(n,dx):
    assert n>=4
    D=np.zeros((n,n));D[0,0]=-1/dx;D[0,1]=1/dx
    D[-1,-2]=-1/dx;D[-1,-1]=1/dx
    for i in range(1,n-1):D[i,i-1]=-1/(2*dx);D[i,i+1]=1/(2*dx)
    H=dx*np.ones(n);H[0]/=2;H[-1]/=2
    B=np.diag([-1]+[0]*(n-2)+[1]);err=np.max(abs(H[:,None]*D+D.T*H[None,:]-B))
    assert err<1e-12
    edge=np.zeros((n,n));edge[0,:3]=[-3,4,-1];edge[-1,-3:]=[1,-4,3]
    for i in range(1,n-1):edge[i,i-1]=-1;edge[i,i+1]=1
    edge/=(2*dx)
    defect=H[:,None]*edge+edge.T*H[None,:]-B
    assert np.max(abs(defect))>.1
    return D,H,np.max(abs(defect))

def derivative(a,D,axis):return np.moveaxis(np.tensordot(D,np.moveaxis(a,axis,0),axes=(1,0)),0,axis)

def run(n):
    g,v,U,dx=d.initial(n)
    T,up,F,den,margin=d.matter(g,U)
    D,h,bad=sbp(n,dx)
    first=np.stack([v,*[derivative(g,D,i) for i in range(3)]],axis=-3)
    source=np.zeros_like(U);source[...,:4]=.5*den[...,None]*np.einsum('...ij,...kij->...k',up,first)
    div=sum(derivative(F[...,i,:],D,i) for i in range(3))
    rhs=source-div
    W=np.multiply.outer(np.multiply.outer(h,h),h)
    integrated=np.sum(W[...,None]*rhs,axis=(0,1,2))
    volumetric=np.sum(W[...,None]*source,axis=(0,1,2))
    oriented=np.zeros(7)
    for i in range(3):
        sl=[slice(None)]*3;sl[i]=-1
        high=np.sum(np.multiply.outer(*[h for j in range(3) if j!=i])[...,None]*F[tuple(sl)][...,i,:],axis=(0,1))
        sl[i]=0
        low=np.sum(np.multiply.outer(*[h for j in range(3) if j!=i])[...,None]*F[tuple(sl)][...,i,:],axis=(0,1))
        oriented+=high-low
    # 3D SBP volume/source/flux identity, all seven conservations.
    err=np.max(abs(integrated+oriented-volumetric))
    assert err<1e-10
    assert np.isfinite(margin) and margin>0
    print('BR310 n',n,'3D instantaneous original G4 worldtube balance',err,'max edge2 non-SBP defect',bad,flush=True)
    print('BR310 signed integrated matter RHS',integrated.tolist(),'oriented flux',oriented.tolist(),'geometric source',volumetric.tolist(),flush=True)
    print('BR310 OPEN next: put SBP flux in full time integrator with compatible SAT/exterior, and preserve covariant gauge constraints',flush=True)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=7);run(p.parse_args().n)
