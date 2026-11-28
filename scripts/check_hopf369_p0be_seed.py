"""Actual AN source seam regression for BE, not a nonlinear PDE solve.
At seam f=f'=0, so the boundary value of C suffices for all second jets.
"""
from check_hopf369_p0an_metric import metric, L, kt
import jax
import jax.numpy as j
import numpy as np

J=-kt/3

def jets(gfun,x):
    def G(X):
        g=gfun(X); d=jax.jacfwd(gfun)(X)
        return .5*j.einsum('al,lij->aij',j.linalg.inv(g),d.transpose(0,2,1)+d-d.transpose(2,0,1))
    def end(y):
        X=j.r_[x,y]; g=gfun(X); I=j.linalg.inv(g); A=G(X); d=jax.jacfwd(G)(X)
        Ric=j.einsum('aija->ij',d)-j.einsum('aiaj->ij',d)+j.einsum('aab,bij->ij',A,A)-j.einsum('ajb,bia->ij',A,A)
        k=-A[3,:3,:3]/j.sqrt(I[3,3])
        return k,Ric[:3,:3]
    H=gfun(j.r_[x,0.])[:3,:3]; I=j.linalg.inv(H)
    kp,Rp=end(0.); km,Rm=end(L); M=(kp+km)/2
    T=-(Rp-Rm)+J*M-J*j.trace(I@M)*H
    tf=lambda A:A-j.trace(I@A)*H/3
    return H,M,T,tf(M),tf(T),kp-km-J*H

def check(x,eps,z):
    base=lambda X:metric(X,eps)
    H,M,T,MT,TT,_=jets(base,x); S=j.linalg.inv(base(j.r_[x,0.]))[3,3]
    # z is the amplitude of a nonconstant spatial smooth reciprocal trial.
    def u(X):
        SS=j.linalg.inv(base(X.at[3].set(0.)))[3,3]
        w=z*(1+X[0]/4)*(1+(j.cosh(X[3]-L/2)/1.25-1)/j.sqrt(SS))
        return 1/(1+w)
    C=-(TT+3*J*(u(j.r_[x,0.])-1)*MT)/(2*S)
    def physical(X):
        y=X[3]; f=y*y*(L-y)**2*(L-2*y)/L**3
        return u(X)**2*base(X).at[:3,:3].add(f*C)
    Hp,Mp,Tp,MTp,TTp,jump=jets(physical,x)
    # Independent negative control: omit coupled correction.
    _,_,_,_,bad,_=jets(lambda X:u(X)**2*base(X),x)
    probe=j.r_[x,L/3]; g=physical(probe); b=base(probe)
    return j.array([j.max(j.abs(TTp)),j.max(j.abs(jump)),j.max(j.abs(bad)),j.max(j.abs(g[:3,3]/g[3,3]-b[:3,3]/b[3,3])),j.abs(g[3,3]-u(probe)**2)])

if __name__=='__main__':
    pts=j.array([[0.,0.,0.],[.2,0.,0.],[.2,.1,0.],[-.3,.2,.1]])
    run=jax.jit(jax.vmap(check,(0,None,None)))
    allrows=[]
    for eps in (0.,.025,-.025):
        for z in (0.,.02,-.02):
            rows=np.asarray(run(pts,eps,z)); m=rows.max(axis=0); allrows.append(rows)
            print('eps',eps,'z',z,'TF, first seam, uncorrected TF, A, phi²',m,flush=True)
            assert max(m[0],m[1],m[3],m[4])<1e-10
            if eps:assert m[2]>1e-6
    print('PASS',sum(len(r) for r in allrows),'actual source points; scalar trace deliberately not constrained',flush=True)
