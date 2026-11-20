"""Geometry-first common-prepotential Galerkin reference, unit AdS radius.
Original F8 TT lifts and weak Israel flux; different finite outer radial domain.
"""
import numpy as np
import sympy as s
from scipy.linalg import solve_banded
from scipy.optimize import brentq
from numpy.polynomial.legendre import leggauss
from math import asinh,sqrt,ceil
from check_f8_tensor_backreaction import angular
from check_f8_common_prepotential import make_evaluator,diagnostics
from check_f8_bianchi_residual import bianchi

def geometry():
    T,Y=s.symbols('T Y');b=s.Function('b')(T);v=b.diff(T);z=b+Y;w=z**-3;k=s.symbols('k');U=s.Function('U')(T,Y);p=U.diff(T)-v*U.diff(Y);q=U.diff(Y);F=q+v*p
    L=-U.diff(T,2)+2*v*U.diff(T,Y)+(1-v*v)*U.diff(Y,2)+(v.diff(T)-3/z)*q-k*k*U
    assert s.simplify((w*p).diff(T)-(w*F).diff(Y)+w*k*k*U+w*L)==0
    P,M=s.symbols('P M');assert s.expand(F.subs({U.diff(T):(P+M+v*(P-M))/2,U.diff(Y):(P-M)/2})-((1+v)*P-(1-v)*M)/2)==0
    t=s.symbols('t',positive=True);Tp=s.sqrt(1+t*t)/t**2;bt=(1/t).diff(t)/Tp
    assert s.simplify(bt+1/s.sqrt(1+t*t))==0
    assert s.simplify(bt.diff(t)/Tp-t**3/(1+t*t)**2)==0
    assert s.simplify(t*t*(-Tp**2+((1/t).diff(t))**2)+1)==0
    a,c,K,W,V=s.symbols('a c K W V');lag=W*((a-V*c)**2-c*c-K)/2
    assert s.expand(a*s.diff(lag,a)-lag-W*(a*a+(1-V*V)*c*c+K)/2)==0
    print('PASS moving pullback, conservative momentum, Israel flux, proper time, acceleration, canonical energy',flush=True)

x,g=leggauss(4);r=(x+1)/2;g=g/2;phi=np.array([1-r,r])
def matrices(Y,b):
    h=Y[1]-Y[0];w=(b+Y[:-1,None]+h*r)**-3;d=np.array([-1,1])/h
    m=np.einsum('eq,q,iq,jq->eij',w,g*h,phi,phi)
    c=np.einsum('eq,q,iq,j->eij',w,g*h,phi,d)
    k=np.einsum('eq,q,i,j->eij',w,g*h,d,d)
    def assemble(a):return np.r_[a[:,0,0],0]+np.r_[0,a[:,1,1]],a[:,0,1],a[:,1,0]
    M,C,K=map(assemble,(m,c,k));md,mu,ml=M
    return M,C,K,np.array([np.r_[0,mu],md,np.r_[ml,0]])

def mv(A,x,transpose=False):
    d,u,l=A
    if transpose:u,l=l,u
    y=d[:,None]*x;y[:-1]+=u[:,None]*x[1:];y[1:]+=l[:,None]*x[:-1];return y

def evolve(n=180,ny=141,dt=.00125,R=4.3,outerY=2.1,exact=False):
    eps=.04;k=np.arange(1,n+1)*np.pi/R;Y=np.linspace(0,outerY,ny)
    a,g=leggauss(160);rr=(a+1)*eps/2
    src=2/R*k*(np.sin(k[:,None]*rr)@(g*rr*eps**4*np.exp(1-1/(1-(rr/eps)**2))*eps/2))
    F=lambda t:asinh(t)-sqrt(1+t*t)/t
    T0=F(1);target=F(11.8);nt=ceil((F(12)-T0)/dt);dt=(F(12)-T0)/nt
    it=round((target-T0)/dt);iy=max(2,round(.06/Y[1]));yi=np.arange(iy-2,iy+3)
    if exact:k=np.array([0.]);src=np.array([0.]);n=1;it=round(.3/dt)
    ti=np.arange(it-2,it+3);U=np.zeros((ny,n));m=np.zeros_like(U)
    if exact:U[:,0]=(1+Y)**4
    snap=[]
    def rhs(U,m,T):
        t=brentq(lambda t:F(t)-T,.5,14);b=1/t;v=-1/sqrt(1+t*t);ds=T-T0
        amp=-6*sqrt(1-v*v)/b*np.exp(1-1/(1-(2*ds/.065-1)**2)) if 0<ds<.065 else 0.
        M,C,K,ab=matrices(Y,b)
        Ut=solve_banded((1,1),ab,m+v*mv(C,U),check_finite=False)
        mt=-v*mv(C,Ut,True)-(1-v*v)*mv(K,U)-mv(M,U)*k*k
        if exact:mt[0]-=4.;mt[-1]+=4.
        else:mt[0]-=b**-3*amp*src;mt[-1]-=(b+Y[-1])**-3*Ut[-1]
        return Ut,mt
    for j in range(it+3):
        T=T0+j*dt
        if j in ti:snap.append(U[yi].copy())
        if j==it+2:break
        a,b=rhs(U,m,T);U1=U+dt*a;m1=m+dt*b
        a,b=rhs(U1,m1,T+dt);U2=.75*U+.25*(U1+dt*a);m2=.75*m+.25*(m1+dt*b)
        a,b=rhs(U2,m2,T+dt/2);U=U/3+2*(U2+dt*a)/3;m=m/3+2*(m2+dt*b)/3
    if exact:
        b=1/brentq(lambda t:F(t)-T0-(it+2)*dt,.5,14);err=np.max(np.abs(U[:,0]-(b+Y)**4));print('manufactured z^4',ny,err,flush=True);return err
    print('reference',R,n,ny,dt,'source tail last 10 k^4 coefficient norm',np.linalg.norm((src*k**4)[-10:]),flush=True)
    return np.array([snap]),(k,T0+ti*dt,Y[yi],eps)

def run():
    geometry();e1=evolve(ny=41,dt=.001,exact=True);e2=evolve(ny=81,dt=.0005,exact=True);assert e2<e1
    xyz,P=angular();F=lambda t:asinh(t)-sqrt(1+t*t)/t;X=np.r_[F(11.8),2.52*np.array([2.,3.,6.])/7,1/11.8+.06]
    for n,ny,dt,R in [(180,71,.00125,4.3),(180,141,.00125,4.3),(180,141,.000625,4.3),(360,141,.000625,4.3),(222,141,.000625,5.3)]:
        H,m=evolve(n,ny,dt,R);v=make_evaluator(H,m,True,xyz,P);a,Q=diagnostics(v,X);b,_=diagnostics(v,X,2e-5)
        assert np.isfinite(a).all() and np.allclose(Q,Q.T,atol=1e-11)
        print('h Q E div',a,'E/h',a[2]/a[0],'jet delta',np.abs(a-b),'Bianchi',bianchi(v,X,2e-4,2e-5),flush=True)
if __name__=='__main__':run()
