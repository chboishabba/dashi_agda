"""Actual physical initial Ricci and wall second-jet diagnostic, not evolution."""
import os
os.environ['AY_BASIS']='poly'
from check_hopf369_p0ay import run, lift, metric, L, kt
import jax
import jax.numpy as j
import numpy as np
from itertools import product

def diagnostic(B=.48,eps=.025,n=4,m=3):
    c=j.asarray(run(B,eps,n,m).reshape(n,n,n,2*m+1))
    def physical(X):
        x=X[:3]/B; polys=[j.ones(3),x]
        for k in range(2,n):polys.append(((2*k-1)*x*polys[-1]-(k-1)*polys[-2])/k)
        P=j.stack(polys[:n],axis=1)*(1-x*x)[:,None]
        t=2*j.pi*X[3]*j.arange(1,m+1)/L
        Y=j.concatenate((j.ones(1),j.cos(t),j.sin(t)))
        z=j.einsum('i,j,k,l,ijkl->',P[0],P[1],P[2],Y,c)
        u=1/(1+lift(X,eps)*z)
        return u*u*metric(X,eps)
    def christ(X):
        g=physical(X); d=jax.jacfwd(physical)(X)
        return .5*j.einsum('al,lij->aij',j.linalg.inv(g),d.transpose(0,2,1)+d-d.transpose(2,0,1))
    def info(X):
        g=physical(X); inv=j.linalg.inv(g); G=christ(X); d=jax.jacfwd(christ)(X)
        Ric=j.einsum('aija->ij',d)-j.einsum('aiaj->ij',d)+j.einsum('aab,bij->ij',G,G)-j.einsum('ajb,bia->ij',G,G)
        return g[:3,:3],-G[3,:3,:3]/j.sqrt(inv[3,3]),Ric[:3,:3],j.sum(inv*Ric)
    bat=jax.jit(jax.vmap(info))
    x=np.array(list(product(np.linspace(-.75*B,.75*B,3),repeat=3)))
    P=np.column_stack((x,np.zeros(len(x)))); Q=P.copy(); Q[:,3]=L
    H,kp,Rp,sp=map(np.asarray,bat(j.asarray(P))); Hm,km,Rm,sm=map(np.asarray,bat(j.asarray(Q)))
    I=np.linalg.inv(H); M=(kp+km)/2; jump=-kt/3
    tr=lambda A:np.einsum('nij,nji->n',I,A)
    J2=-(Rp-Rm)+jump*M-jump*tr(M)[:,None,None]*H
    TF=J2-tr(J2)[:,None,None]*H/3
    norm=lambda A:np.sqrt(np.maximum(0,np.einsum('nij,nji->n',I@A,I@A)))
    err=np.max(norm(kp-km-jump*H)); traceerr=np.max(abs(sp-sm+2*tr(J2)))
    assert np.max(abs(H-Hm))<1e-10 and err<1e-10 and traceerr<1e-8
    # Lambda=-6: scalar residuals are R+12. Correct only the second
    # covariant normal jets; the induced metric and first jets stay fixed.
    Dp=-TF/2+(sp+12)[:,None,None]*H/6
    Dm=TF/2+(sm+12)[:,None,None]*H/6
    rem=np.max(norm(J2+Dp-Dm)); scalar=np.max(abs(np.concatenate((sp+12-2*tr(Dp),sm+12-2*tr(Dm)))))
    assert rem<1e-10 and scalar<1e-10
    print(dict(collar_second_jet_residual=rem,collar_scalar_residual=scalar,correction_plus_max=np.max(norm(Dp)),correction_minus_max=np.max(norm(Dm))),flush=True)
    print(dict(points=len(x),first_jump_max=err,scalar_trace_identity_max=traceerr,second_jet_trace_max=np.max(abs(tr(J2))),tracefree_second_jet_max=np.max(norm(TF)),tracefree_second_jet_rms=np.sqrt(np.mean(norm(TF)**2))),flush=True)

if __name__=='__main__':diagnostic()
