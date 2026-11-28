#!/usr/bin/env python3
"""Actual AN/BB initial wall tensor pullback; no evolved wall/bulk solve."""
import os
os.environ.setdefault('JAX_ENABLE_X64','true')
os.environ.setdefault('XLA_FLAGS','--xla_cpu_multi_thread_eigen=false intra_op_parallelism_threads=1')
import numpy as np
import jax
import jax.numpy as j

L=2*np.log(2); h0=.8; kt=3.6
# Literal AN metric from #1554 check_hopf369_p0an_metric.py.
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

# Literal BB seed: p=p_t=0, B=0, sigma and Q from the mean of the two
# one-sided extrinsic-curvature tensors of the AN metric.
def seed(x,eps):
    H=metric(j.r_[x,0.],eps)[:3,:3]; I=j.linalg.inv(H)
    def k(y):
        X=j.r_[x,y]; return -conn(X,eps)[3,:3,:3]/j.sqrt(j.linalg.inv(metric(X,eps))[3,3])
    a,b=k(0.),k(L); M=(a+b)/2; sig=j.trace(I@M); Q=I@M-sig*j.eye(3)/3
    h=j.zeros((4,4)).at[0,0].set(-1.).at[1:,1:].set(H)
    m=j.zeros((4,4)).at[0,0].set(sig).at[1:,1:].set(H@(Q+sig*j.eye(3)/3))
    jump=-kt/3
    return h,m,m+jump*h/2,m-jump*h/2,a-b+kt*H/3

def phi(U):
    t=U[0]; c=(1-t*t)/(1+t*t); s=2*t/(1+t*t)
    R=j.array([[c,-s,0.],[s,c,0.],[0.,0.,1.]])
    return j.r_[t,R@U[1:]]

def jet(h,K):
    I=j.linalg.inv(h); return -j.trace(I@K)*K+2*K@I@K

def require(ok,label):
    if not bool(ok): raise RuntimeError(label)

maxima={k:0. for k in ('original_AN_jump','trace','israel','second_jet_jump','jet_covariance','mixed_K','frozen_K')}
for eps in (.025,-.025,0.):
    for x in (j.array([.1,-.15,.07]),j.array([-.12,.08,.16])):
        U=j.r_[0.,x]; J=jax.jacfwd(phi)(U); h,m,kp,km,jump3=seed(phi(U)[1:],eps)
        change=lambda T:J.T@T@J
        H,M,Kp,Km=map(change,(h,m,kp,km)); I=j.linalg.inv(H)
        e={'original_AN_jump':j.max(j.abs(jump3)), 'trace':j.abs(j.trace(I@M)),
           'israel':j.max(j.abs(Kp-Km+kt*H/3)),
           'second_jet_jump':j.max(j.abs(jet(H,Kp)-jet(H,Km))),
           'jet_covariance':max(float(j.max(j.abs(jet(H,Kp)-change(jet(h,kp))))),float(j.max(j.abs(jet(H,Km)-change(jet(h,km)))))),
           'mixed_K':j.max(j.abs(Kp[0,1:])),
           'frozen_K':j.max(j.abs(Kp-kp))}
        for name,value in e.items(): maxima[name]=max(maxima[name],float(value))
        require(np.linalg.eigvalsh(np.asarray(H))[0]<0 and np.all(np.linalg.eigvalsh(np.asarray(H))[1:]>0),'Lorentz signature')
        require(max(float(e[k]) for k in ('original_AN_jump','trace','israel','second_jet_jump','jet_covariance'))<1e-10,'wall tensor covariance')
require(maxima['mixed_K']>1e-3 and maxima['frozen_K']>1e-3,'frozen negative control')
print('PASS six initial wall samples',maxima,flush=True)
