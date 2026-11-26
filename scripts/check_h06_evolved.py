#!/usr/bin/env python3
"""Same-reference curvature on original BB/BC finite difference jets, not a continuum solve.
Usage: python check_h06_evolved.py /path/to/pinned/donor/scripts
"""
import os,sys,hashlib
from pathlib import Path
os.environ.setdefault('JAX_ENABLE_X64','true')
os.environ.setdefault('XLA_FLAGS','--xla_cpu_multi_thread_eigen=false intra_op_parallelism_threads=1')
def require(ok,label):
    if not bool(ok):raise RuntimeError(label)
root=Path(sys.argv[1]).resolve()
for name,sha in [('bb','ca3c34308b22ef6d0a41906d1b2c71acb97eb718'),('bc','5854e7466708408dc5b719aa7d6f5266bc1db44e')]:
    b=(root/f'check_hopf369_p0{name}.py').read_bytes()
    require(hashlib.sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==sha,'donor '+name)
s=(root/'check_hopf369_p0an_metric.py').read_text();s=s[s.index('L=2*np.log(2)'):].split('def geometry')[0]
s='\n'.join(x for x in s.splitlines() if x.strip() and not x.strip().startswith('#'))
hashval=2166136261
for c in s:hashval=((hashval^ord(c))*16777619)&0xffffffff
require(len(s)==690 and hashval==0xa873fb8,'AN selected source text')
sys.path.insert(0,str(root))
import numpy as np
import jax
import jax.numpy as j
from check_hopf369_p0bc import wall,normal_rhs,residual,kt

def jet(a,sp,idx):
    d=lambda a,k:(np.roll(a,-1,k)-np.roll(a,1,k))/(2*sp[k])
    da=np.stack([d(a,k) for k in range(4)],-1);dd=np.stack([d(da,k) for k in range(4)],-1)
    for k in range(4):dd[...,k,k]=(np.roll(a,-1,k)-2*a+np.roll(a,1,k))/sp[k]**2
    return a[idx],da[idx],dd[idx]
def phi(U):
    t=U[0];c=(1-t*t)/(1+t*t);s=2*t/(1+t*t)
    R=j.array([[c,-s,0.],[s,c,0.],[0.,0.,1.]])
    return j.r_[t,R@U[1:4],U[4]]
def metric(U,centre,A,B,C):
    d=U[:4]-centre;n=U[4]
    jets=A+j.einsum('aijk,k->aij',B,d)+.5*j.einsum('aijkl,k,l->aij',C,d,d)
    return j.eye(5).at[:4,:4].set(jets[0]+2*n*jets[1]+n*n*jets[2]+n**3*jets[3]/3)
def pull(U,*args):
    J=jax.jacfwd(phi)(U);return J.T@metric(phi(U),*args)@J
def conn(g,U,args):
    h=g(U,*args);d=jax.jacfwd(g,0)(U,*args)
    return .5*j.einsum('al,lij->aij',j.linalg.inv(h),d.transpose(0,2,1)+d-d.transpose(2,0,1))
def ric(g,U,args):
    G=conn(g,U,args);d=jax.jacfwd(lambda X:conn(g,X,args))(U)
    return j.einsum('aija->ij',d)-j.einsum('aiaj->ij',d)+j.einsum('aab,bij->ij',G,G)-j.einsum('ajb,bia->ij',G,G)
@jax.jit
def compare(U,centre,A,B,C):
    args=(centre,A,B,C);X=phi(U);J=jax.jacfwd(phi)(U)
    g=metric(X,*args);gp=pull(U,*args);r=ric(metric,X,args);rp=ric(pull,U,args)
    return r,rp,r+4*g,rp+4*gp,g,gp,J
cov=diff=res=mixed=freeze=jump=third=0.;count=0
for eps in (.025,-.025,0.):
    h,M,sp=wall(eps);dt,dx,*_=sp
    print('original wall',eps,h.shape,flush=True)
    Ds=[];Fs=[]
    for side in (1,-1):
        K=M-side*kt*h/6;D=normal_rhs(h,K,sp);eta=1e-5
        F=(normal_rhs(h+2*eta*K,K+eta*D,sp)-normal_rhs(h-2*eta*K,K-eta*D,sp))/(2*eta)
        Ds.append(D);Fs.append(F)
        for idx in ((3,4,5,3),(4,5,3,4)):
            mixed=max(mixed,float(np.max(abs(M[idx][0,1:]))))
            centre=np.array([(idx[0]-2)*dt,*[(k-4)*dx for k in idx[1:]]]);t=centre[0]
            c=(1-t*t)/(1+t*t);s=2*t/(1+t*t);Rinv=np.array([[c,s,0.],[-s,c,0.],[0.,0.,1.]])
            A,B,C=map(np.stack,zip(*(jet(a,sp,idx) for a in (h,K,D,F))))
            for radius in (0.,.01):
                n=side*radius;U=np.r_[t,Rinv@centre[1:],n]
                r,rp,E,Ep,g,gp,J=map(np.asarray,compare(j.asarray(U),j.asarray(centre),j.asarray(A),j.asarray(B),j.asarray(C)))
                err=max(np.max(abs(rp-J.T@r@J)),np.max(abs(Ep-J.T@E@J)));cov=max(cov,float(err));require(err<1e-9,'covariance')
                ev=np.linalg.eigvalsh(gp);require(ev[0]<0 and np.all(ev[1:]>0),'signature')
                a,b,v=residual(h+2*n*K+n*n*D+n**3*F/3,K+n*D+n*n*F/2,D+n*F,sp)
                ref=np.zeros((5,5));ref[:4,:4]=a[idx];ref[4,4]=b[idx];ref[:4,4]=ref[4,:4]=v[idx]
                diff=max(diff,float(np.max(abs(E-ref))));res=max(res,float(np.max(abs(ref))))
                frozen=J.copy();frozen[1:4,0]=0;freeze=max(freeze,float(np.max(abs(gp-frozen.T@g@frozen))))
                count+=1
    for idx in ((3,4,5,3),(4,5,3,4)):
        jump=max(jump,float(np.max(abs(Ds[0][idx]-Ds[1][idx]))));third=max(third,float(np.max(abs(Fs[0][idx]-Fs[1][idx]))))
    print('sector',eps,'cov',cov,'BC diff',diff,flush=True)
require(jump<1e-10 and mixed>1e-8 and freeze>1e-3,'retained signed normal/mixed sectors')
print('PASS',count,dict(cov=cov,BC_difference=diff,BC_residual=res,wall_mixed=mixed,frozen=freeze,D_jump=jump,F_jump=third),flush=True)
