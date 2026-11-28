"""BB: original AN timelike wall, local RK4 replay; not bulk evolution."""
from check_hopf369_p0an_metric import metric, conn, L, kt
import numpy as np
import jax
import jax.numpy as j

def seed(x,eps):
    def H(z): return metric(j.r_[z,0.],eps)[:3,:3]
    def G(z):
        h=H(z); d=jax.jacfwd(H)(z)
        return .5*j.einsum('al,lij->aij',j.linalg.inv(h),d.transpose(0,2,1)+d-d.transpose(2,0,1))
    h=H(x); I=j.linalg.inv(h); g=G(x); d=jax.jacfwd(G)(x)
    R=j.einsum('aija->ij',d)-j.einsum('aiaj->ij',d)+j.einsum('aab,bij->ij',g,g)-j.einsum('ajb,bia->ij',g,g)
    def k(y):
        X=j.r_[x,y]; return -conn(X,eps)[3,:3,:3]/j.sqrt(j.linalg.inv(metric(X,eps))[3,3])
    a,b=k(0.),k(L); M=(a+b)/2; s=j.trace(I@M)
    return h,I,g,j.sum(I*R),s,I@M-s*j.eye(3)/3,a-b+kt*h/3
batch=jax.jit(jax.vmap(seed,(0,None)))

def setup(N,eps,dx,center=0.):
    x=np.arange(-N,N+1)*dx; X=np.stack(np.meshgrid(x+center,x,x,indexing='ij'),-1)
    assert np.max(np.sum(X*X,-1))<1
    pts=X.reshape(-1,3); out=[[] for _ in range(7)]
    for i in range(0,len(pts),512):
        a=pts[i:i+512]; b=np.pad(a,((0,512-len(a)),(0,0)),mode='edge')
        for o,v in zip(out,batch(j.asarray(b),eps)):o.append(np.asarray(v)[:len(a)])
    H,I,G,R0,s,Q,J=[np.concatenate(o).reshape(X.shape[:3]+o[0].shape[1:]) for o in out]
    assert np.max(abs(J))<1e-10
    d=lambda f,k:(np.roll(f,-1,k)-np.roll(f,1,k))/(2*dx)
    grad=lambda f:np.stack([d(f,k) for k in range(3)],-1)
    divQ=sum(d(Q[...,k,:],k) for k in range(3))+np.einsum('...iik,...kj->...j',G,Q)-np.einsum('...kij,...ik->...j',G,Q)
    Q2=np.einsum('...ij,...ji->...',Q,Q)
    dot=lambda a,b:np.einsum('...i,...ij,...j->...',a,I,b)
    def rhs(Y):
        p,v,s=Y[...,0],Y[...,1],Y[...,2]; B=Y[...,3:]; dp=grad(p); D=grad(dp)
        for k in range(3):D[...,k,k]=(np.roll(p,-1,k)-2*p+np.roll(p,1,k))/dx**2
        D-=np.einsum('...kij,...k->...ij',G,dp)
        lap=np.einsum('...ij,...ij->...',I,D); e=np.exp(-2*p)
        R=e*(R0-4*lap-2*dot(dp,dp))
        DB=grad(B)-np.einsum('...kij,...k->...ij',G,B)
        divB=e*(np.einsum('...ij,...ij->...',I,DB)+dot(dp,B))
        return np.concatenate((v[...,None],((-12+3*(kt/3)**2-4*s*s/3-Q2+2*e*dot(B,B)-R-12*v*v)/6)[...,None],(divB-4*v*s)[...,None],divQ+3*np.einsum('...i,...ij->...j',dp,Q)+grad(s)/3-3*v[...,None]*B),-1)
    Y=np.zeros(X.shape[:3]+(6,));Y[...,2]=s
    return Y,rhs,H,Q

def step(Y,f,t):
    a=f(Y);b=f(Y+t*a/2);c=f(Y+t*b/2);d=f(Y+t*c)
    return Y+t*(a+2*b+2*c+d)/6

def audit(Y,A,C,f,H0,Q,dt,core):
    p,v,s=Y[...,0],Y[...,1],Y[...,2]; B=Y[...,3:]; H=np.exp(2*p)[...,None,None]*H0
    h=np.zeros(p.shape+(4,4));h[...,0,0]=-1;h[...,1:,1:]=H; I=np.linalg.inv(h)
    M=np.zeros_like(h);M[...,0,0]=s;M[...,0,1:]=M[...,1:,0]=B;M[...,1:,1:]=H@(Q+s[...,None,None]*np.eye(3)/3)
    tr=lambda T:np.trace(I@T,axis1=-2,axis2=-1)
    jmp=-kt/3; K=M+jmp*h/2; L=M-jmp*h/2
    jet=lambda Z:-tr(Z)[...,None,None]*Z+2*Z@I@Z
    ma=lambda a:float(np.max(abs(a[core])))
    # independent time finite differences; spatial terms use same FD operator.
    ptt=(C[...,0]-2*p+A[...,0])/dt**2
    return dict(p=ma(p),mixed=ma(B),trace=ma(tr(M)),israel=ma(K-L-jmp*h),jet=ma(jet(K)-jet(L)),gauss=6*ma(ptt-f(Y)[...,1]),codazzi=ma(((C-A)/(2*dt)-f(Y))[...,2:]))

def main():
    dx=.025; dt=.012; N=15; core=(slice(13,-13),)*3
    Y,f,H,Q=setup(N,.025,dx); A=step(Y,f,dt); C=step(A,f,dt)
    a=audit(A,Y,C,f,H,Q,dt,core);print('base',a,flush=True)
    B=step(Y,f,dt/2); D=step(B,f,dt/2); E=step(D,f,dt/2)
    b=audit(D,B,E,f,H,Q,dt/2,core);print('half',b,flush=True)
    assert b['gauss']<a['gauss'] and b['codazzi']<a['codazzi']
    assert max(a[k] for k in ('trace','israel','jet'))<1e-10
    print('time_refine',np.max(abs((A-D)[core])),flush=True)
    Z,g,_,_=setup(N,-.025,dx); Z=step(step(Z,g,dt),g,dt)
    err=np.max(abs((C-Z*np.array([1,1,-1,-1,-1,-1]))[core])); assert err<1e-11
    back=step(Y,f,-dt); err2=np.max(abs((A-back*np.array([1,-1,1,-1,-1,-1]))[core]));assert err2<1e-11
    print('signed/time parity',err,err2,flush=True)
    z,g,_,_=setup(11,.025,dx,2*dx); z=step(step(z,g,dt),g,dt)
    err=np.max(abs(C[15:20,13:18,13:18]-z[9:14,9:14,9:14]));assert err<1e-11
    print('independent chart overlap 125',err,flush=True)
if __name__=='__main__':main()
