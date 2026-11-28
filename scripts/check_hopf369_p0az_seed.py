"""AZ: actual AM/AN seam data -> analytic volume/shape initial 2-jet.
No integration of the normal CK PDE or continuum evolution asserted.
"""
from check_hopf369_p0an_metric import metric, conn, L, kt
import jax
import jax.numpy as j
import numpy as np
from itertools import product


def run(eps=.025):
    jump=-kt/3
    def wall(x):
        return metric(j.concatenate((x,j.zeros(1))),eps)[:3,:3]
    def gamma(x):
        H=wall(x); d=jax.jacfwd(wall)(x)
        return .5*j.einsum('al,lij->aij',j.linalg.inv(H),d.transpose(0,2,1)+d-d.transpose(2,0,1))
    def seam(x):
        H=wall(x); I=j.linalg.inv(H); G=gamma(x); d=jax.jacfwd(gamma)(x)
        Ric=j.einsum('aija->ij',d)-j.einsum('aiaj->ij',d)+j.einsum('aab,bij->ij',G,G)-j.einsum('ajb,bia->ij',G,G)
        R=j.sum(I*Ric)
        def k(y):
            X=j.concatenate((x,j.array([y]))); g=metric(X,eps)
            return -conn(X,eps)[3,:3,:3]/j.sqrt(j.linalg.inv(g)[3,3])
        return H,k(0.),k(L),R
    pts=j.asarray(list(product((-.3,0.,.3),repeat=3)))
    H,kp,km,R=map(np.asarray,jax.jit(jax.vmap(seam))(pts))
    I=np.linalg.inv(H); M=(kp+km)/2
    tr=lambda X:np.trace(I@X,axis1=1,axis2=2)
    norm=lambda X:np.sqrt(np.maximum(0,np.trace(I@X@I@X,axis1=1,axis2=2)))
    def scale(a,X):return a[:,None,None]*X
    m=tr(M)/3; A=2*I@(M-scale(m,H)); A2=A@A
    trA2=np.trace(A2,axis1=1,axis2=2)
    def jets(sign):
        t=m+sign*jump/2
        q=(R-12*t*t-trA2/4+12)/6
        B=-sign*2*jump*A
        k=scale(t,H)+H@A/2
        D=scale(q+2*t*t,H)+scale(2*t,H@A)+H@(B+A2)/2
        scalar=R-2*tr(D)+3*np.trace(I@k@I@k,axis1=1,axis2=2)-tr(k)**2
        Nn=-3*m+sign*jump/2 # common lapse chosen N0=1
        return k,D,scalar,Nn
    Kp,Dp,sp,Np=jets(1); Km,Dm,sm,Nm=jets(-1)
    result=dict(eps=eps,points=len(pts),min_wall_eig=float(np.min(np.linalg.eigvalsh(H))),
      seed_first_jump=float(np.max(norm(kp-km-jump*H))),
      seed_k_recovery=float(max(np.max(norm(Kp-kp)),np.max(norm(Km-km)))),
      shape_nonzero=float(np.max(norm(H@A))),
      full_J2=float(np.max(norm(Dp-Dm))),
      scalar=float(max(np.max(abs(sp+12)),np.max(abs(sm+12)))),
      lapse_jump=float(np.max(abs(Np-Nm-jump))),
      lapse_mean=float(np.max(abs((Np+Nm)/2+tr(M)))))
    assert result['min_wall_eig']>0
    assert max(result[k] for k in ('seed_first_jump','seed_k_recovery','full_J2','scalar','lapse_jump','lapse_mean'))<1e-10
    if eps!=0: assert result['shape_nonzero']>1e-6
    print(result,flush=True)

if __name__=='__main__':
    for eps in (0.,.025,-.025):run(eps)
