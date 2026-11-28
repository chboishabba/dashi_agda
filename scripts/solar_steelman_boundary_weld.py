"""Causal external source and final seven-port Foster termination on loaded orbit.
Intermediate ports removed by prior mediator inverse. Normalized finite model.
"""
import sympy as S
from solar_steelman_loaded_material import loaded,cross_band_reaction
from solar_steelman_material_metric import run as metric
I=S.I

def zero(A):return all(S.expand(x)==0 for x in A)

def branch(w,v,X):
    n=X.rows;Id=S.eye(n);assert X==X.T
    Y=X-w/(v*v-w*w)*Id
    a=1+sum(abs(x) for x in Y)
    L=(Y+a*Id)/w;K=w*a*Id
    assert all(L[j,j]>sum(abs(L[j,k]) for k in range(n) if k!=j) for j in range(n))
    assert K[0,0]>0
    assert zero(w*L-K/w+w/(v*v-w*w)*Id-X)
    return L,K

def check(w,v,L,K,current,effort,blocked):
    q=current/(I*w);x=I*w*current/(v*v-w*w);z=x/(I*w)
    assert zero(I*w*q-current) and zero(I*w*x-current+v*v*z) and zero(I*w*z-x)
    assert zero(I*w*L*current+K*q+x-effort)
    xb=blocked;zb=xb/(I*v)
    assert zero(I*v*xb+v*v*zb) and zero(I*v*zb-xb)
    return q,x,z,xb,zb

def ledger():
    i,q,x,z,d,L,K,v=S.symbols('i q x z d L K v',real=True)
    assert S.expand(i*L*d+q*K*i+x*(i-v*v*z)+v*v*z*x-i*(L*d+K*q+x))==0
    s,vs,vr,j,R=S.symbols('s vs vr j R',real=True)
    assert S.expand(vs*i-vr*j+i*(2*s-i-vs)+j*(vr-R*j)-s*s+(s-i)**2+R*j*j)==0

def run(m=None):
    if m is None:m=metric()
    a=S.Rational(1,2);U=S.eye(15)
    hi=loaded(m,a,S.Integer(2),U[:,0],U[1:8,:]);lo=loaded(m,a,S.Integer(1),U[:,1],U[8:15,:])
    cross_band_reaction(m,a,[hi,lo])
    sh=U[:,0];rl=U[8:15,:];ih=S.ones(1,1);il=lo['p'];R=lo['load']
    vh=sh.T*hi['v'];vl=rl*lo['v'];Xh=-sh.T*hi['X']*sh;Xl=-rl*lo['X']*rl.T
    Lh,Kh=branch(S.Integer(2),S.Integer(1),Xh)
    Ll,Kl=branch(S.Integer(1),S.Integer(2),Xl)
    check(S.Integer(2),S.Integer(1),Lh,Kh,ih,ih-vh,-sh.T*lo['v'])
    check(S.Integer(1),S.Integer(2),Ll,Kl,il,vl-R*il,rl*hi['v'])
    assert zero(vh+I*Xh*ih-ih)
    assert zero(vl-I*Xl*il-R*il)
    assert S.expand(S.re((il.H*R*il)[0]))==1
    ledger()
    print('PASS causal source and full seven-port final load, positive matrix storage, blocked efforts retained',flush=True)
    print('PASS arbitrary-state boundary energy identity: incident minus reflected minus final load',flush=True)
    print('LIMIT occupied harmonic boundary weld; ideal mediator phase and full distributed stability still open',flush=True)
if __name__=='__main__':run()
