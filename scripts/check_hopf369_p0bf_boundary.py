"""BF boundary-enriched solve and numerical inverse/positivity diagnostics."""
from check_hopf369_p0bf import *
from scipy.linalg import svdvals
import json

def bounds(c,n,m):
    C=np.abs(c.reshape(9,n,2*m+1)).sum(axis=2)
    deg=np.array([0,1,1,1,2,2,2,2,2])/2
    mult=np.array([1,1,1,1,1,1,1,1,2])
    # For each squared-radius interval, use decreasing envelope at left,
    # increasing factors at right, and lift <= 1, |Fourier| <= 1.
    return max((1-a)**2/(1+10*a)*np.sum(C*(mult*b**deg)[:,None]*(b/(.10+b))**np.arange(n)[None,:]) for a,b in zip(np.arange(256)/256,np.arange(1,257)/256))

def run(n=4,m=2,power=10):
    eps=.025; X=sample(power,123); x=sample(7,789)[:,:3]
    Z=np.vstack([np.c_[x,np.zeros(len(x))],np.c_[x,np.full(len(x),L)]])
    X=np.vstack([X,Z]); B,V=prepare(X,eps,n,m); c=np.zeros(V.shape[-1]); Y=sample(power,456); T,W=prepare(Y,eps,n,m)
    rms=lambda a:float(np.sqrt(np.mean(a*a)))
    for k in range(8):
        v=V@c; r=np.asarray(Rbatch(*B,v)); A=np.einsum('ni,nij->nj',np.asarray(DJ(*B,v)),V)
        dc=lstsq(A,-r,cond=1e-9,lapack_driver='gelsy')[0]
        for a in (1.,.5,.25,.125):
            cand=c+a*dc
            if bounds(cand,n,m)<.2 and rms(np.asarray(Rbatch(*B,V@cand)))<=rms(r):
                c=cand;break
        else:break
        if np.max(abs((V@dc)[:,0]))<1e-10:break
    r=np.asarray(Rbatch(*B,V@c)); A=np.einsum('ni,nij->nj',np.asarray(DJ(*B,V@c)),V)
    norms=np.linalg.norm(A,axis=0); sv=svdvals(A/norms); e,g,I,G,Ric=map(np.asarray,Ebatch(*T,W@c)); diag=np.sqrt(np.diagonal(g,axis1=1,axis2=2)); eig=np.linalg.eigvalsh(g/diag[:,:,None]/diag[:,None,:]); assert eig.min()>0
    print('boundary enriched','train bulk',rms(r[:2**power]),'train seam',rms(r[2**power:]),'test',rms(e),'max',np.max(abs(e)), 'w bound',bounds(c,n,m),'normalized sampled metric min eig',eig.min(),'scaled Jacobian sv min/max',sv[-1],sv[0],flush=True)
    x=np.array([[0,0,0],[.2,0,0],[.2,.1,0],[-.3,.2,.1]])
    Z=np.vstack([np.c_[x,np.zeros(len(x))],np.c_[x,np.full(len(x),L)]])
    S,U=prepare(Z,eps,n,m); f,g,I,G,Ric=map(np.asarray,Ebatch(*S,U@c))
    k=-G[:,3,:3,:3]/np.sqrt(I[:,3,3,None,None]); H=g[:4,:3,:3]; M=(k[:4]+k[4:])/2; Hi=np.linalg.inv(H)
    J2=-(Ric[:4,:3,:3]-Ric[4:,:3,:3])+J*M-J*np.trace(Hi@M,axis1=1,axis2=2)[:,None,None]*H
    trace=np.trace(Hi@J2,axis1=1,axis2=2); tf=J2-trace[:,None,None]*H/3
    print('independent seam',np.max(abs(k[:4]-k[4:]-J*H)),np.max(abs(tf)),np.max(abs(trace)),'scalar',np.max(abs(f)),'trace identity',np.max(abs(f[:4]-f[4:]+2*trace)),flush=True)
    yy,wt=np.polynomial.legendre.leggauss(24); y=L*(yy+1)/2; coords=np.c_[np.repeat(x,len(y),axis=0),np.tile(y,len(x))]
    u=1/(1+np.asarray(jax.jit(jax.vmap(lambda X:basis(X,eps,n,m)@c))(j.array(coords))))
    print('fibre length deltas',((u.reshape(-1,len(y))-1)@wt)*L/2,flush=True)
    # Pullback signed comparator (not independent negative-amplitude optimization).
    Yr=Y.copy(); Yr[:,3]=L-Yr[:,3]; cr=c.reshape(9,n,2*m+1).copy();cr[:,:,2::2]*=-1;cr=cr.ravel()
    N,Vr=prepare(Yr,-eps,n,m); er=np.asarray(Rbatch(*N,Vr@cr)); print('signed reflected residual',np.max(abs(e-er)),flush=True)
    N0,V0=prepare(Y,0.,n,m); zero=np.asarray(Rbatch(*N0,V0@np.zeros_like(c)));print('zero comparator',np.max(abs(zero)),flush=True)
    assert np.max(abs(e-er))<1e-8 and np.max(abs(zero))<1e-8
    print('COEFFICIENTS',json.dumps(c.tolist()),flush=True)

if __name__=='__main__':run()
