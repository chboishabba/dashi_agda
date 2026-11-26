"""BG: independent endpoint scalar-jet controls on original BF metric.
Finite equality-constrained collocation, not continuum certification.
"""
import check_hopf369_p0bf as bf
from check_hopf369_p0bf import *
from scipy.linalg import svd

def enriched(X,eps,n,m):
    x,y,z,t=X; r=x*x+y*y+z*z; d=1-r
    H=j.array([1,x,y,z,x*y,x*z,y*z,x*x-y*y,3*z*z-r])
    radial=j.array([(r/(.10+r))**k for k in range(n)])
    p=j.array([t*t*(1-t/L)**3/2,(L-t)**2*(t/L)**3/2])
    return j.concatenate([basis(X,eps,n,m),(d*d/(1+10*r)*H[:,None,None]*radial[None,:,None]*p[None,None,:]).ravel()])

def ej(X,eps,n,m):
    f=lambda X:enriched(X,eps,n,m)
    return f(X),jax.jacfwd(f)(X),jax.jacfwd(jax.jacfwd(f))(X)

bf.BJ=jax.jit(jax.vmap(ej,(0,None,None,None)),static_argnums=(2,3))

def run():
    eps=.025;n=4;m=2
    X=sample(10,123); Y=sample(10,456)
    x=sample(5,789)[:,:3]; z=sample(7,987)[:,:3]
    ends=lambda x:np.vstack([np.c_[x,np.zeros(len(x))],np.c_[x,np.full(len(x),L)]])
    B,V=prepare(X,eps,n,m); S,U=prepare(ends(x),eps,n,m); T,W=prepare(Y,eps,n,m); Q,Z=prepare(ends(z),eps,n,m)
    c=np.zeros(V.shape[-1]); rms=lambda a:float(np.sqrt(np.mean(a*a)))
    for it in range(8):
        v=V@c;s=U@c;r=np.asarray(Rbatch(*B,v));f=np.asarray(Rbatch(*S,s)); A=np.einsum('ni,nij->nj',np.asarray(DJ(*B,v)),V); E=np.einsum('ni,nij->nj',np.asarray(DJ(*S,s)),U)
        scale=np.maximum(np.linalg.norm(np.vstack([A,E]),axis=0),1e-12); A=A/scale;E=E/scale
        l,d,h=svd(E,full_matrices=True); rank=np.sum(d>d[0]*1e-10); p=h[:rank].T@((l[:,:rank].T@(-f))/d[:rank]); N=h[rank:].T
        dc=(p+N@lstsq(A@N,-r-A@p,cond=1e-9,lapack_driver='gelsy')[0])/scale
        for a in (1.,.5,.25,.125):
            cand=c+a*dc
            if np.max(abs((V@cand)[:,0]))<.2 and rms(np.asarray(Rbatch(*S,U@cand)))<=max(rms(f)*1.01,1e-10) and rms(np.asarray(Rbatch(*B,V@cand)))<=max(rms(r)*1.001,1e-10):c=cand;break
        else:break
        print('iteration',it,'rank',rank,'bulk',rms(np.asarray(Rbatch(*B,V@c))),'seam',rms(np.asarray(Rbatch(*S,U@c))),flush=True)
        if np.max(abs((V@dc)[:,0]))<1e-10:break
    f,g,I,G,Ric=map(np.asarray,Ebatch(*Q,Z@c)); N=len(z); k=-G[:,3,:3,:3]/np.sqrt(I[:,3,3,None,None]);H=g[:N,:3,:3];M=(k[:N]+k[N:])/2;Hi=np.linalg.inv(H)
    J2=-(Ric[:N,:3,:3]-Ric[N:,:3,:3])+J*M-J*np.trace(Hi@M,axis1=1,axis2=2)[:,None,None]*H
    trace=np.trace(Hi@J2,axis1=1,axis2=2);tf=J2-trace[:,None,None]*H/3
    e=np.asarray(Rbatch(*T,W@c)); print('final',len(c),'test bulk RMS/max',rms(e),np.max(abs(e)),'test seam RMS/max',rms(f),np.max(abs(f)),'trace max',np.max(abs(trace)),'TF max',np.max(abs(tf)),'first max',np.max(abs(k[:N]-k[N:]-J*H)),flush=True)
    q=Z@c; u=1/(1+q[:,0]); coeff=6/u*np.linalg.inv(Q[0][:,0])[:,3,3]; q2=q.copy(); q2[:,-1]-=f/coeff
    f2,g2,I2,G2,R2=map(np.asarray,Ebatch(*Q,q2)); k2=-G2[:,3,:3,:3]/np.sqrt(I2[:,3,3,None,None]); M2=(k2[:N]+k2[N:])/2
    JJ=-(R2[:N,:3,:3]-R2[N:,:3,:3])+J*M2-J*np.trace(Hi@M2,axis1=1,axis2=2)[:,None,None]*H
    print('exact endpoint jet replay',len(q2),'scalar max',np.max(abs(f2)),'full J2 max',np.max(abs(JJ)),'first jet change',np.max(abs(k2-k)),flush=True)
    assert np.max(abs(f2))<1e-9 and np.max(abs(JJ))<1e-6
    import json
    print('COEFFICIENTS',json.dumps(c.tolist()),flush=True)
if __name__=='__main__':run()
