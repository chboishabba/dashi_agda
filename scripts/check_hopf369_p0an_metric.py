"""Finite-box Q1 test of actual AM periodic Hopf seed (not continuum acceptance)."""
import os
os.environ.setdefault('JAX_ENABLE_X64','true')
os.environ.setdefault('XLA_FLAGS','--xla_cpu_multi_thread_eigen=false intra_op_parallelism_threads=1')
import jax
import jax.numpy as j
import numpy as np
from itertools import product
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import spsolve

L=2*np.log(2); h0=.8; kt=3.6

def metric(X,eps):
    x=X[:3]; y=X[3]; r2=x@x; fac=2*(1+r2)/(h0*(1-r2)**2)
    df=2/h0*((1-r2)**-2+2*(1+r2)*(1-r2)**-3)
    pull=fac*j.eye(3)+2*df*j.outer(x,x)
    X0=fac*x; X1,X2,X3=X0; D=1+X0@X0
    A=2*j.array([2*X1*X3-2*X2,2*X1+2*X2*X3,1-X1**2-X2**2+X3**2])/D**2
    a=eps*pull@A; gamma=4/(h0**2*(1-r2)**2)*j.eye(3)
    S=1+(a@a)/gamma[0,0]; H=gamma+j.outer(a,a)
    b=j.cosh(y-L/2)/1.25
    Q=gamma+(b*b-1)*H/j.sqrt(S)
    return j.block([[Q+j.outer(a,a),a[:,None]],[a[None,:],j.ones((1,1))]])

def conn(X,eps):
    g=metric(X,eps); d=jax.jacfwd(metric,0)(X,eps)
    return .5*j.einsum('al,lij->aij',j.linalg.inv(g),d.transpose(0,2,1)+d-d.transpose(2,0,1))

def geometry(X,eps):
    g=metric(X,eps); inv=j.linalg.inv(g); G=conn(X,eps); d=jax.jacfwd(conn,0)(X,eps)
    Ric=j.einsum('aija->ij',d)-j.einsum('aiaj->ij',d)+j.einsum('aab,bij->ij',G,G)-j.einsum('ajb,bia->ij',G,G)
    return inv,j.sqrt(j.linalg.det(g)),j.sum(inv*Ric)

batch=jax.jit(jax.vmap(geometry,(0,None)))

def sample(pts,eps):
    out=[[],[],[]]
    # Fixed batch length avoids retracing remainder.
    for i in range(0,len(pts),512):
        q=pts[i:i+512]; n=len(q); q=np.pad(q,((0,512-n),(0,0)),mode='edge')
        for a,v in zip(out,batch(j.asarray(q),eps)): a.append(np.asarray(v)[:n])
    return tuple(np.concatenate(a) for a in out)

def assemble(rows,cols,data,n):
    return coo_matrix((data.ravel(),(rows.ravel(),cols.ravel())),shape=(n,n)).tocsr()

def run(N,M,eps,B=.36):
    ds=np.array([2*B/N]*3+[L/M]); vol=np.prod(ds)/16
    cells=np.array(list(product(range(N),range(N),range(N),range(M))))
    offs=np.array(list(product((0,1),repeat=4))); xi=np.array(list(product((-1/np.sqrt(3),1/np.sqrt(3)),repeat=4)))
    nshape=(N+1,N+1,N+1,M); n=np.prod(nshape)
    node=cells[:,None,:]+offs[None,:,:]; node[...,3]%=M
    ids=np.ravel_multi_index(node.transpose(2,0,1),nshape)
    centers=(cells+.5)*ds+np.array([-B,-B,-B,0]); pts=(centers[:,None,:]+xi[None,:,:]*ds/2).reshape(-1,4)
    inv,det,R=sample(pts,eps); nc=len(cells); inv=inv.reshape(nc,16,4,4); det=det.reshape(nc,16); R=R.reshape(nc,16)
    if eps==0: assert np.max(abs(R+12))<1e-9
    factors=(1+xi[:,None,:]*(2*offs[None,:,:]-1))/2
    P=factors.prod(axis=2); D=np.stack([np.prod(np.delete(factors,k,axis=2),axis=2)*(2*offs[None,:,k]-1)/ds[k] for k in range(4)],axis=2)
    W=det*vol; K=np.einsum('qia,cqab,qjb,cq->cij',D,inv,D,W,optimize=True)
    # Dirichlet correction on outer cube, periodic seam y=0.
    rows=np.broadcast_to(ids[:,:,None],K.shape); cols=np.broadcast_to(ids[:,None,:],K.shape)
    mat=assemble(rows,cols,K,n)
    # Seam Q1 integration: cells with y index zero, lower y nodes.
    face=cells[:,3]==0; fids=ids[face][:,offs[:,3]==0]; fcent=centers[face].copy(); fcent[:,3]=0
    x3=np.array(list(product((-1/np.sqrt(3),1/np.sqrt(3)),repeat=3))); o3=offs[offs[:,3]==0,:3]
    fP=np.prod((1+x3[:,None,:]*(2*o3[None,:,:]-1))/2,axis=2)
    fpts=fcent[:,None,:]+np.pad(x3,((0,0),(0,1)))[None,:,:]*ds/2
    fm=jax.jit(jax.vmap(metric,(0,None)))(j.asarray(fpts.reshape(-1,4)),eps)
    fw=np.sqrt(np.linalg.det(np.asarray(fm)[:,:3,:3])).reshape(-1,8)*np.prod(ds[:3])/8
    fr=np.broadcast_to(fids[:,:,None],(len(fids),8,8)); fc=np.broadcast_to(fids[:,None,:],fr.shape)
    grid=np.indices(nshape).reshape(4,-1); free=np.flatnonzero(np.all((grid[:3]>0)&(grid[:3]<N),axis=0)); u=np.ones(n)
    def residual(u,jac=False):
        v=u[ids]@P.T; f=u[fids]@fP.T
        loc=np.einsum('cq,qi->ci',W*(R/6*v+2*v**3),P); floc=np.einsum('cq,qi->ci',fw*kt/3*(f-f*f),fP)
        res=mat@(u-1); np.add.at(res,ids.ravel(),loc.ravel()); np.add.at(res,fids.ravel(),floc.ravel())
        if not jac:return res
        J=np.einsum('cq,qi,qj->cij',W*(R/6+6*v*v),P,P,optimize=True)
        Jf=np.einsum('cq,qi,qj->cij',fw*kt/3*(1-2*f),fP,fP,optimize=True)
        return res,mat+assemble(rows,cols,J,n)+assemble(fr,fc,Jf,n)
    for it in range(12):
        r,J=residual(u,True); err=np.max(abs(r[free]))
        if err<2e-11:break
        u[free]-=spsolve(J[free][:,free],r[free])
    else:raise AssertionError('Newton nonconvergence')
    assert np.min(u)>0 and err<2e-11
    if eps==0:assert np.max(abs(u-1))<1e-10
    # One-sided Q1 derivative jump in the physical seed normal. Tangential
    # derivatives coincide on the periodic seam, so cancel in the jump.
    U=u.reshape(nshape); jdy=((U[:,:,:,1]-2*U[:,:,:,0]+U[:,:,:,-1])/ds[3]).ravel()
    face3=np.ravel_multi_index(np.unravel_index(fids,nshape)[:3],nshape[:3])
    jump=(jdy[face3]@fP.T)*np.sqrt(np.linalg.inv(np.asarray(fm))[:,3,3]).reshape(-1,8)
    f=u[fids]@fP.T; target=kt/3*(f-f*f)
    rms=lambda a:np.sqrt(np.sum(fw*a*a)/np.sum(fw))
    print(dict(B=B,trace_rms=rms(jump-target),trace_target_rms=rms(target),center=float(U[N//2,N//2,N//2,0]),N=N,M=M,eps=eps,iterations=it,weak_residual=err,umin=u.min(),umax=u.max(),max_correction=np.max(abs(u-1)),R_min=R.min(),R_max=R.max()),flush=True)
    return u.reshape(nshape)

if __name__=='__main__':
    run(4,6,0.)
    for N,M in ((4,6),(6,8)):
        u=run(N,M,.025); v=run(N,M,-.025)
        err=np.max(abs(u-v[:,:,:,[0]+list(range(M-1,0,-1))]))
        assert err<1e-10
        print('signed circle-reflection replay',err,flush=True)
