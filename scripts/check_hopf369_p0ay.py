"""AY: seam-conforming spectral approximation on the original AM metric."""
import os
os.environ.setdefault('JAX_ENABLE_X64','true')
os.environ.setdefault('XLA_FLAGS','--xla_cpu_multi_thread_eigen=false intra_op_parallelism_threads=1')
import numpy as np
import sympy as s
import jax
import jax.numpy as j
from itertools import product
from scipy.linalg import lstsq
from numpy.polynomial.legendre import leggauss, Legendre
from check_hopf369_p0an_metric import metric,conn,geometry,L,kt

def exact():
    w,d,k,R,lap,grad=s.symbols('w d k R lap grad',real=True); u=1/(1+w)
    assert s.cancel(d/(1+w)**2+k*(u-u*u)/3-(d+k*w/3)/(1+w)**2)==0
    F=lap/(1+w)**2-2*grad/(1+w)**3+R*u/6+2*u**3
    assert s.cancel(F*(1+w)**3-((1+w)*lap-2*grad+R*(1+w)**2/6+2))==0
    print('PASS reciprocal wall and bulk BIDI',flush=True)

def lift(X,eps):
    S=j.linalg.inv(metric(X.at[3].set(0.),eps))[3,3]
    return 1+(j.cosh(X[3]-L/2)/1.25-1)/j.sqrt(S)

def coefficients(X,eps):
    inv,vol,R=geometry(X,eps); G=conn(X,eps); drift=-j.einsum('ij,kij->k',inv,G)
    f=lift(X,eps); df=jax.grad(lift,0)(X,eps); ddf=jax.hessian(lift,0)(X,eps)
    return inv,vol,R,drift,f,df,j.sum(inv*ddf)+drift@df

batch=jax.jit(jax.vmap(coefficients,(0,None)))
def sample(pts,eps):
    out=[[] for _ in range(7)]
    for i in range(0,len(pts),128):
        a=pts[i:i+128]; n=len(a); a=np.pad(a,((0,128-n),(0,0)),mode='edge')
        for o,x in zip(out,batch(j.asarray(a),eps)):o.append(np.asarray(x)[:n])
    return tuple(np.concatenate(o) for o in out)

def design(pts,eps,B,n,m):
    inv,vol,R,drift,f,df,lf=sample(pts,eps)
    if os.environ.get('AY_BASIS')=='poly':
        pol=[Legendre.basis(k)*(Legendre([1])-Legendre([0,1])**2) for k in range(n)]
        a=np.stack([f(pts[:,:3]/B) for f in pol],axis=2)
        da=np.stack([f.deriv()(pts[:,:3]/B)/B for f in pol],axis=2)
        dda=np.stack([f.deriv(2)(pts[:,:3]/B)/B**2 for f in pol],axis=2)
    else:
        freq=np.arange(1,n+1)*np.pi/(2*B); t=(pts[:,:3,None]+B)*freq
        a=np.sin(t); da=np.cos(t)*freq; dda=-a*freq**2
    om=np.arange(1,m+1)*2*np.pi/L; y=pts[:,3,None]*om
    Y=np.column_stack((np.ones(len(pts)),np.cos(y),np.sin(y)))
    DY=np.column_stack((np.zeros(len(pts)),-np.sin(y)*om,np.cos(y)*om))
    DDY=np.column_stack((np.zeros(len(pts)),-np.cos(y)*om**2,-np.sin(y)*om**2))
    idx=np.array(list(product(range(n),range(n),range(n),range(2*m+1))))
    v=[a[:,k,idx[:,k]] for k in range(3)]+[Y[:,idx[:,3]]]
    d=[da[:,k,idx[:,k]] for k in range(3)]+[DY[:,idx[:,3]]]
    dd=[dda[:,k,idx[:,k]] for k in range(3)]+[DDY[:,idx[:,3]]]
    P=np.prod(v,axis=0); dP=np.stack([d[k]*np.prod([v[l] for l in range(4) if k!=l],axis=0) for k in range(4)],axis=1)
    lap=np.einsum('ni,nik->nk',drift,dP)
    for i in range(4):
        lap+=inv[:,i,i,None]*dd[i]*np.prod([v[l] for l in range(4) if i!=l],axis=0)
        for k in range(i):lap+=2*inv[:,i,k,None]*d[i]*d[k]*np.prod([v[l] for l in range(4) if l!=i and l!=k],axis=0)
    return f[:,None]*P,f[:,None,None]*dP+df[:,:,None]*P[:,None,:],f[:,None]*lap+2*np.einsum('ni,nij,njk->nk',df,inv,dP)+lf[:,None]*P,inv,R,vol

def points(B,n,m):
    x,wx=leggauss(n); y,wy=leggauss(m)
    return np.array(list(product(B*x,B*x,B*x,L*(y+1)/2))),np.prod(np.array(list(product(B*wx,B*wx,B*wx,L*wy/2))),axis=1)

def residual(D,c,jac=False):
    W,dW,LW,inv,R,vol=D; w=W@c; dw=np.einsum('nik,k->ni',dW,c); lap=LW@c
    F=(1+w)*lap-2*np.einsum('ni,nij,nj->n',dw,inv,dw)+R/6*(1+w)**2+2
    if not jac:return F,w
    return F,w,W*lap[:,None]+(1+w[:,None])*LW-4*np.einsum('ni,nij,njk->nk',dw,inv,dW)+R[:,None]/3*(1+w[:,None])*W

def run(B,eps,n,m):
    pts,wt=points(B,n+2,2*m+4); D=design(pts,eps,B,n,m); scale=np.sqrt(wt*D[-1]); c=np.zeros(D[0].shape[1])
    rms=lambda F,w:np.sqrt(np.sum(F*F*w)/np.sum(w))
    for it in range(6):
        F,w,J=residual(D,c,True); dc=lstsq(scale[:,None]*J,-scale*F,lapack_driver='gelsy')[0]; c+=dc
        if np.max(abs(dc))<1e-12:break
    pts2,wt2=points(B,n+3,2*m+5); T=design(pts2,eps,B,n,m); F,w=residual(T,c)
    assert np.min(1+w)>0
    # Analytic all-box positivity: |basis|<=1 and 0<lift<=1.
    amplitude=np.sum(abs(c)); assert amplitude<1
    # Ground state transform weight phi=u² f has exact linearized seam.
    inv,vol,R,drift,f,df,lf=sample(pts2,eps)
    W,dW,LW=T[:3]; dw=np.einsum('nik,k->ni',dW,c); lapw=LW@c
    u=1/(1+w); du=-u[:,None]**2*dw
    lapu=-u**2*lapw+2*u**3*np.einsum('ni,nij,nj->n',dw,inv,dw)
    lphi=u*u*lf+4*u*np.einsum('ni,nij,nj->n',du,inv,df)+2*f*(u*lapu+np.einsum('ni,nij,nj->n',du,inv,du))
    rate=-lphi/(u*u*f)+R/6+6*u*u
    assert np.min(rate)>0
    xx=np.array(list(product(np.linspace(-B,B,5),repeat=3))); a=np.column_stack((xx,np.zeros(len(xx)))); b=a.copy(); b[:,3]=L
    A=design(a,eps,B,n,m); C=design(b,eps,B,n,m); wa=A[0]@c; wb=C[0]@c
    jump=np.einsum('ni,ni->n',A[3][:,3,:]/np.sqrt(A[3][:,3,3,None]),np.einsum('nik,k->ni',A[1]-C[1],c))
    wall=(jump+kt*wa/3)/(1+wa)**2
    assert np.max(abs(wa-wb))<1e-12 and np.max(abs(wall))<1e-11
    # Independent test quadrature; physical residual F(u).
    print(dict(basis=os.environ.get("AY_BASIS","sin"),B=B,eps=eps,n=n,m=m,coefficient_l1=amplitude,sampled_linear_coercivity_min=np.min(rate),coeffs=len(c),iterations=it+1,test_rms=rms(F/(1+w)**3,wt2*T[-1]),baseline_rms=rms(T[4]/6+2,wt2*T[-1]),wall_max=np.max(abs(wall)),u_min=np.min(1/(1+w)),u_max=np.max(1/(1+w))),flush=True)
    return c

if __name__=='__main__':
    import sys
    exact(); B=float(sys.argv[1]) if len(sys.argv)>1 else .36
    eps=float(sys.argv[2]) if len(sys.argv)>2 else .025
    for n,m in ((2,1),(3,2),(4,3)):run(B,eps,n,m)
