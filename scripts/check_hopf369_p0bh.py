"""BH: actual BG endpoint-function lift, finite-difference tangential jets."""
import check_hopf369_p0bg as bg
from check_hopf369_p0bf import *
from check_hopf369_p0an_metric import h0
import json,sys
from pathlib import Path

def qjet(X,eps,c):
    f=lambda X:bg.enriched(X,eps,4,2)@c
    return j.concatenate([j.atleast_1d(f(X)),jax.grad(f)(X),jax.hessian(f)(X).ravel()])
def bfun(x,eps,c):
    def side(t):
        X=j.r_[x,t]; B,dB,ddB=block_jets(X,eps); q=qjet(X,eps,c)
        return -res(B,dB,ddB,q)/(6*j.linalg.inv(B[0])[3,3]*(1+q[0]))
    return j.stack([side(0.),side(L)])
Bfun=jax.jit(jax.vmap(bfun,(0,None,None)))
Qfun=jax.jit(jax.vmap(qjet,(0,None,None)))
def bvalues(x,eps,c):
    out=[]
    for k in range(0,len(x),64):
        a=x[k:k+64]; N=len(a); a=np.pad(a,((0,64-N),(0,0)),mode='edge')
        out.append(np.asarray(Bfun(j.array(a),eps,c))[:N])
    return np.concatenate(out)
def bjets(x,eps,c,step):
    h=step*(1-np.linalg.norm(x,axis=1)); eye=np.eye(3); n=len(x); offsets=[np.zeros(3)]
    for i in range(3):offsets.extend([eye[i],-eye[i]])
    for i,k in ((0,1),(0,2),(1,2)):offsets.extend([eye[i]+eye[k],eye[i]-eye[k],-eye[i]+eye[k],-eye[i]-eye[k]])
    z=np.array(offsets)[:,None,:]*h[None,:,None]+x[None,:,:]
    a=bvalues(z.reshape(-1,3),eps,c).reshape(len(offsets),n,2); b=a[0]
    d=np.zeros((n,2,3)); dd=np.zeros((n,2,3,3))
    for i in range(3):
        p,m=a[1+2*i:3+2*i];d[:,:,i]=(p-m)/(2*h[:,None]);dd[:,:,i,i]=(p+m-2*b)/h[:,None]**2
    for l,(i,k) in enumerate(((0,1),(0,2),(1,2))):
        pp,pm,mp,mm=a[7+4*l:11+4*l];dd[:,:,i,k]=dd[:,:,k,i]=(pp-pm-mp+mm)/(4*h[:,None]**2)
    return b,d,dd
def profile(t,width):
    def one(s):
        v=np.maximum(1-s/width,0.)
        return np.array([s*s*v**5/2,s*v**5-2.5*s*s*v**4/width,v**5-10*s*v**4/width+10*s*s*v**3/width**2]).T
    p=one(t); m=one(L-t);m[:,1]*=-1
    return np.stack([p,m],axis=1)
def lift(q,t,bd,width):
    b,d,dd=bd; P=profile(t,width);v,p,pp=P[:,:,0],P[:,:,1],P[:,:,2]
    out=q.copy();out[:,0]+=np.sum(v*b,axis=1);out[:,1:4]+=np.einsum('ns,nsi->ni',v,d);out[:,4]+=np.sum(p*b,axis=1)
    a=out[:,5:].reshape(-1,4,4);a[:,:3,:3]+=np.einsum('ns,nsij->nij',v,dd);a[:,:3,3]+=np.einsum('ns,nsi->ni',p,d);a[:,3,:3]+=np.einsum('ns,nsi->ni',p,d);a[:,3,3]+=np.sum(pp*b,axis=1)
    return out
def evaluate_points(X,eps,c):return tuple(map(np.asarray,BB(j.array(X),eps))),np.asarray(Qfun(j.array(X),eps,c))
def run(c):
    eps=.025; X=sample(8,456); B,q=evaluate_points(X,eps,c); bd=bjets(X[:,:3],eps,c,2e-4); bd2=bjets(X[:,:3],eps,c,1e-4)
    rms=lambda a:float(np.sqrt(np.mean(a*a)))
    print('endpoint function max',np.max(abs(bd[0])),'baseline RMS/max',rms(np.asarray(Rbatch(*B,q))),np.max(abs(np.asarray(Rbatch(*B,q)))),flush=True)
    for width in (L,L/2,L/4,L/8,L/16):
        a=lift(q,X[:,3],bd,width); a2=lift(q,X[:,3],bd2,width); r,g,*_=map(np.asarray,Ebatch(*B,a2));r0=np.asarray(Rbatch(*B,a)); scale=(1-np.sum(X[:,:3]**2,axis=1))*h0/2; D=np.c_[np.repeat(scale[:,None],3,axis=1),np.ones(len(X))]; eig=np.linalg.eigvalsh(g*D[:,:,None]*D[:,None,:])
        print('width/L',width/L,'RMS',rms(r),'max',np.max(abs(r)),'FD difference',np.max(abs(r-r0)),'min normalized eig',eig.min(),'w max',np.max(abs(a2[:,0])),'lift max',np.max(abs(a2[:,0]-q[:,0])),flush=True)
        assert eig.min()>0 and np.min(1+a2[:,0])>0
    x=sample(5,987)[:,:3];Z=np.vstack([np.c_[x,np.zeros(len(x))],np.c_[x,np.full(len(x),L)]])
    Q,v=evaluate_points(Z,eps,c);b=bvalues(x,eps,c);bb=np.tile(b,(2,1));d=np.zeros((len(Z),2,3));dd=np.zeros((len(Z),2,3,3));v2=lift(v,Z[:,3],(bb,d,dd),L/4)
    r,g,I,G,Ric=map(np.asarray,Ebatch(*Q,v2));N=len(x);k=-G[:,3,:3,:3]/np.sqrt(I[:,3,3,None,None]);H=g[:N,:3,:3];M=(k[:N]+k[N:])/2;Hi=np.linalg.inv(H);J2=-(Ric[:N,:3,:3]-Ric[N:,:3,:3])+J*M-J*np.trace(Hi@M,axis1=1,axis2=2)[:,None,None]*H
    print('seam',len(Z),'scalar max',np.max(abs(r)),'J2 normalized max',np.max(abs(Hi@J2)),'first normalized max',np.max(abs(Hi@(k[:N]-k[N:]-J*H))),'first q identical',np.array_equal(v2[:,:5],v[:,:5]),flush=True)
    assert np.max(abs(r))<1e-8 and np.max(abs(Hi@J2))<1e-8 and np.array_equal(v2[:,:5],v[:,:5])
    neg=c.copy();neg[:180].reshape(9,4,5)[:,:,[2,4]]*=-1;neg[180:]=c[180:].reshape(9,4,2)[:,:,::-1].ravel();p=bvalues(x,-eps,neg);z=bvalues(x,0.,np.zeros_like(c));print('signed b parity max',np.max(abs(p-b[:,::-1])),'zero b max',np.max(abs(z)),flush=True)
    assert np.max(abs(p-b[:,::-1]))<1e-8 and np.max(abs(z))<1e-8
if __name__=='__main__':
    c=np.array(json.loads(Path(sys.argv[1]).read_text().split('COEFFICIENTS ')[-1]));assert len(c)==252
    run(c)
