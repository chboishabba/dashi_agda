"""BF: coupled BE metric collocation on the whole coordinate ball; not continuum certification."""
from check_hopf369_p0an_metric import metric,L,kt
from check_hopf369_p0be_seed import jets
import jax
import jax.numpy as j
import numpy as np
from scipy.linalg import lstsq
from scipy.stats import qmc
J=-kt/3

def wall_coeff(x,eps):
    def wall(x):return metric(j.r_[x,0.],eps)[:3,:3]
    def cov(x):return metric(j.r_[x,0.],eps)[:3,3]
    def alpha(x):return 1/j.sqrt(j.linalg.inv(metric(j.r_[x,0.],eps))[3,3])
    H=wall(x); a=cov(x); I=j.linalg.inv(H); d=jax.jacfwd(wall)(x)
    G=.5*j.einsum('al,lij->aij',I,d.transpose(0,2,1)+d-d.transpose(2,0,1))
    da=jax.jacfwd(cov)(x); al=alpha(x); dl=jax.grad(alpha)(x)
    M=-(.5*(da+da.T)-j.einsum('k,kij->ij',a,G))/al
    tf=lambda T:T-j.trace(I@T)*H/3
    MT=tf(M); TT=J/al**2*tf(j.outer(dl,a)+j.outer(a,dl))+J*(2-(a@I@a)/al**2)*MT
    return -al**2*TT/2,-al**2*3*J*MT/2,al

def blocks(X,eps):
    y=X[3]; C0,C1,al=wall_coeff(X[:3],eps)
    f=y*y*(L-y)**2*(L-2*y)/L**3
    return j.stack([metric(X,eps).at[:3,:3].add(f*C0),j.zeros((4,4)).at[:3,:3].set(f*C1)])

def block_jets(X,eps):
    fn=lambda X:blocks(X,eps)
    return fn(X),jax.jacfwd(fn)(X),jax.jacfwd(jax.jacfwd(fn))(X)

def basis(X,eps,n,m):
    x,y,z,t=X; r=x*x+y*y+z*z; delta=1-r
    H=j.array([1,x,y,z,x*y,x*z,y*z,x*x-y*y,3*z*z-r])
    s=r/(.10+r); radial=j.array([s**k for k in range(n)])
    Y=j.array([1.]+[f(k*2*j.pi*t/L) for k in range(1,m+1) for f in (j.cos,j.sin)])
    al=1/j.sqrt(j.linalg.inv(metric(X.at[3].set(0.),eps))[3,3])
    lift=1+(j.cosh(t-L/2)/1.25-1)*al
    return (lift*delta**2/(1+10*r)*H[:,None,None]*radial[None,:,None]*Y[None,None,:]).ravel()

def basis_jets(X,eps,n,m):
    fn=lambda X:basis(X,eps,n,m)
    return fn(X),jax.jacfwd(fn)(X),jax.jacfwd(jax.jacfwd(fn))(X)

def curvature(g,d,dd):
    I=j.linalg.inv(g); T=d.swapaxes(-1,-2)+d-j.moveaxis(d,-1,-3)
    G=.5*j.einsum('al,lij->aij',I,T)
    di=-j.einsum('ai,ijk,jb->abk',I,d,I)
    dt=dd.swapaxes(-2,-3)+dd-j.moveaxis(dd,-2,-4)
    dg=.5*(j.einsum('alk,lij->aijk',di,T)+j.einsum('al,lijk->aijk',I,dt))
    Ric=j.einsum('aija->ij',dg)-j.einsum('aiaj->ij',dg)+j.einsum('aab,bij->ij',G,G)-j.einsum('ajb,bia->ij',G,G)
    return I,G,j.sum(I*Ric),Ric

def evaluate(B,dB,ddB,q):
    w=q[0]; dw=q[1:5]; ddw=q[5:].reshape(4,4)
    u=1/(1+w); du=-u*u*dw; ddu=2*u**3*j.outer(dw,dw)-u*u*ddw
    c=j.array([u*u,u*u*(u-1)]); c1=j.array([2*u,3*u*u-2*u]); c2=j.array([2.,6*u-2])
    g=j.einsum('k,kij->ij',c,B)
    d=j.einsum('k,kija->ija',c,dB)+j.einsum('k,kij,a->ija',c1,B,du)
    dd=j.einsum('k,kijab->ijab',c,ddB)+j.einsum('k,kija,b->ijab',c1,dB,du)+j.einsum('k,kijb,a->ijab',c1,dB,du)+j.einsum('k,kij,ab->ijab',c2,B,j.outer(du,du))+j.einsum('k,kij,ab->ijab',c1,B,ddu)
    I,G,R,Ric=curvature(g,d,dd)
    return R+12,g,I,G,Ric

res=lambda B,dB,ddB,q:evaluate(B,dB,ddB,q)[0]
Rbatch=jax.jit(jax.vmap(res)); DJ=jax.jit(jax.vmap(jax.grad(res,3)))
Ebatch=jax.jit(jax.vmap(evaluate)); BB=jax.jit(jax.vmap(block_jets,(0,None)))
BJ=jax.jit(jax.vmap(basis_jets,(0,None,None,None)),static_argnums=(2,3))

def sample(power,seed):
    z=qmc.Sobol(4,scramble=True,seed=seed).random_base2(power)
    r=z[:,0]; cos=2*z[:,1]-1; az=2*np.pi*z[:,2]; s=np.sqrt(1-cos*cos)
    return np.column_stack((r*s*np.cos(az),r*s*np.sin(az),r*cos,L*z[:,3]))

def prepare(X,eps,n,m):
    B,dB,ddB=map(np.asarray,BB(j.array(X),eps))
    b,db,ddb=map(np.asarray,BJ(j.array(X),eps,n,m))
    V=np.concatenate([b[:,None,:],db.transpose(0,2,1),ddb.reshape(len(X),-1,16).transpose(0,2,1)],axis=1)
    return (B,dB,ddB),V

def solve(eps,n,m,power):
    X=sample(power,123); B,V=prepare(X,eps,n,m); c=np.zeros(V.shape[-1]); T,W=prepare(sample(power,456),eps,n,m)
    rms=lambda a:np.sqrt(np.mean(a*a))
    base=np.asarray(Rbatch(*T,W@c)); initial=rms(base)
    for k in range(6):
        v=V@c; r=np.asarray(Rbatch(*B,v)); A=np.einsum('ni,nij->nj',np.asarray(DJ(*B,v)),V)
        dc=lstsq(A,-r,cond=1e-9,lapack_driver='gelsy')[0]
        for a in (1.,.5,.25,.125):
            cand=c+a*dc
            if np.max(abs((V@cand)[:,0]))<.2 and rms(np.asarray(Rbatch(*B,V@cand)))<=rms(r):
                c=cand;break
        else:break
        if np.max(abs((V@dc)[:,0]))<1e-10:break
    out=np.asarray(Rbatch(*T,W@c)); tr=np.asarray(Rbatch(*B,V@c))
    print('solve',eps,n,m,len(c),len(X),'train',rms(tr),'test',rms(out),'base',initial,'max',np.max(abs(out)),'w range',(W@c)[:,0].min(),(W@c)[:,0].max(),flush=True)
    x=np.array([[0,0,0],[.2,0,0],[.2,.1,0],[-.3,.2,.1]])
    Z=np.vstack([np.c_[x,np.zeros(len(x))],np.c_[x,np.full(len(x),L)]])
    S,U=prepare(Z,eps,n,m); e,g,I,G,Ric=map(np.asarray,Ebatch(*S,U@c))
    k=-G[:,3,:3,:3]/np.sqrt(I[:,3,3,None,None]); H=g[:4,:3,:3]; Mi=(k[:4]+k[4:])/2; Hi=np.linalg.inv(H)
    J2=-(Ric[:4,:3,:3]-Ric[4:,:3,:3])+J*Mi-J*np.trace(Hi@Mi,axis1=1,axis2=2)[:,None,None]*H
    trace=np.trace(Hi@J2,axis1=1,axis2=2); tf=J2-trace[:,None,None]*H/3
    print('seam',np.max(abs(k[:4]-k[4:]-J*H)),np.max(abs(tf)),np.max(abs(trace)), 'scalar',np.max(abs(e)),'trace identity',np.max(abs(e[:4]-e[4:]+2*trace)),flush=True)
    yy,wt=np.polynomial.legendre.leggauss(24); y=L*(yy+1)/2
    coords=np.c_[np.repeat(x,len(y),axis=0),np.tile(y,len(x))]
    u=1/(1+np.asarray(jax.jit(jax.vmap(lambda X:basis(X,eps,n,m)@c))(j.array(coords))))
    print('fibre length deltas',((u.reshape(-1,len(y))-1)@wt)*L/2,flush=True)
    return c

if __name__=='__main__':
    for eps in (.025,-.025,0.):
        x=j.array([.2,.1,0.]); C0,C1,al=wall_coeff(x,eps); H,M,T,MT,TT,_=jets(lambda X:metric(X,eps),x)
        assert np.max(abs(C0+al**2*TT/2))<1e-10 and np.max(abs(C1+al**2*3*J*MT/2))<1e-10
    print('wall coeff parity PASS',flush=True)
    import sys
    n,m,p=map(int,sys.argv[1:]) if len(sys.argv)>1 else (2,1,9)
    solve(.025,n,m,p)
