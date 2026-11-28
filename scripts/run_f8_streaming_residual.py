"""Original F8 modal stages + separate checkpointed residual consumer.
Diagnostic run; signed Gauss integrals and FP majorants are NOT certificates.
"""
import argparse,json,math,time,hashlib
from pathlib import Path
import numpy as np
from scipy.optimize import brentq
from scipy.integrate import quad
from numpy.polynomial.legendre import leggauss
import sympy as S
from f8_fused_step import weights
from run_f8_common_modal_box import stage
from ksw668_f8_tt_multipole import F
from check_f8_streaming_residual import Ledger,jets,digest,exact_majorant
from fractions import Fraction as Q

R,Y,eps=3.012,4.032,.04
T0=F(1);span=F(12)-T0

def clock(T):
    t=brentq(lambda t:F(t)-T,.5,25);b=1/t;v=-b/math.sqrt(1+b*b)
    return b,v,1-v*v,b/(1+b*b)**2

def pulse(T):
    b,v,s,a=clock(T);u=2*(T-T0)/.065-1
    if abs(u)>=1:return 0.,0.
    f=math.exp(1-1/(1-u*u));ft=-4*u*f/(.065*(1-u*u)**2)
    A=-6/(b*math.sqrt(1+b*b));At=6*(1+2*b*b)*v/(b*b*(1+b*b)**1.5)
    return A*f,At*f+A*ft

def dual_builder(k,receiver):
    # Exact flux lift of the original *continuous* E4 or SMS scalar window,
    # with nonzero trace and compact normal taper; not optimized parametrix.
    b,u,K=S.symbols('b u K',real=True);v=-b/S.sqrt(1+b*b);s=1/(1+b*b)
    J=-b*b/S.sqrt(1+b*b);H=S.sqrt(1+b*b);f=S.exp(1-1/(1-u*u))
    dt=lambda a:v*S.diff(a,b)+10*S.diff(a,u)
    scale,extra,sign=((S.Rational(1,4),0,-1),(S.Rational(1,2),2,1))[receiver]
    a2=-scale*b*b*H*H*f;a1=-scale*b*b*(J+extra*H)*f;a0=sign*scale*b*b*f
    q=dt(dt(a2))-dt(a1)-K*K*a0
    A=b**3*f;D=(b**3*q-v*dt(A))/s
    ev=S.lambdify((b,u,K),[A,dt(A),dt(dt(A)),D,dt(D),dt(dt(D))],'numpy',cse=True)
    norm=.1*quad(lambda x:math.exp(1-1/(1-x*x)),-1,1,epsabs=1e-13)[0]
    def dual(T,y):
        u=10*(T-T0-(span-.15));b,v,s,a=clock(T)
        if abs(u)>=1:return np.zeros_like(k),np.zeros_like(k)
        A,At,Att,D,Dt,Dtt=[z/norm for z in ev(b,u,k)]
        f=1-(y/Y)**2;C=f**3;Cy=-6*y*f*f/Y**2;Cyy=-6*f*f/Y**2+24*y*y*f/Y**4
        V=A+D*y;Vt=At+Dt*y
        phi=V*C;py=D*C+V*Cy;pty=Dt*C+Vt*Cy;pyy=2*D*Cy+V*Cyy
        L=-(Att+Dtt*y)*C+2*v*pty+s*pyy+(a-3/(b+y))*py-k*k*phi
        return phi,L
    return dual

def run(work,n,ny,dt,budget,receiver):
    dy=Y/(ny-1);nt=math.ceil(span/dt);h=span/nt;k=np.arange(1,n+1)*np.pi/R;lam=k*k
    assert h<=.9/(k[-1]+81/(16*dy)+25.5) and dy<=1/48
    x,w=leggauss(512);r=eps*(1+x)/2
    src=math.sqrt(2/R)*eps**4*(np.sin(k[:,None]*r)@(w*r*np.exp(1-1/(1-(r/eps)**2))*eps/2))
    def coeff(T):b,v,_,_=clock(T);return v,b,pulse(T)[0]
    source=lambda T:pulse(T)[0]*src;source_dt=lambda T:pulse(T)[1]*src
    dual=dual_builder(k,receiver);work.mkdir(parents=True,exist_ok=True)
    p=work/f'residual-{n}-{ny}-{dt}-{receiver}.npz'
    identity=dict(n=n,ny=ny,h=h,source=digest(src),receiver=receiver,driver=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    if p.exists():ledger,X=Ledger.load(p,identity)
    else:ledger,X=Ledger(n),np.zeros((6,ny,n))
    assert 0<=ledger.cursor<=nt+1;initial=ledger.cursor;start=time.monotonic();out,A,D=[np.empty_like(X) for _ in range(3)]
    exact_sample=None
    while ledger.cursor<nt+1:
        T=T0+ledger.cursor*h;left=jets(X,clock(T)[1],dy)
        for q,(inp,dst,t) in enumerate(((X,A,T),(A,D,T+h),(D,out,T+h/2))):
            v,b,amp=coeff(t);z,lo,hi,*_=weights(b,dy,ny);stage(inp,X,dst,h,q,dy,v,amp,src,lam,z,lo,hi)
        right=jets(out,clock(T+h)[1],dy)
        # Coarse global analytic bounds for original t in [1,13] incl lookahead.
        ledger.add(left,right,T,h,dy,k,clock,source,(1/13,1,1,.5),source_dt,dual)
        if ledger.cursor==111:
            # Exact reference for one real slab/mode; original compact source
            # |c|<eps^6, |amp|<=12 during pulse, |amp'|<10000.
            exact=exact_majorant(left[:,:,0],right[:,:,0],h,dy,(Q(22,7)/Q('3.012'))**2,(Q(1,13),1,1,Q(1,2)),12*Q('0.04')**6,10000*Q('0.04')**6)
            exact_sample=[str(z) for z in exact]
        X,out=out,X
        if ledger.cursor%64==0 or ledger.cursor==nt+1 or time.monotonic()-start>=budget:
            ledger.save(p,identity,X)
            check,Z=Ledger.load(p,identity);assert check.cursor==ledger.cursor and np.array_equal(Z,X) and np.array_equal(check.a,ledger.a)
            if time.monotonic()-start>=budget:break
    return dict(initial=initial,cursor=ledger.cursor,end=nt+1,n=n,ny=ny,dt=h,receiver=receiver,ledger=ledger.a.tolist(),exact_sample=exact_sample,state_sha=digest(X),seconds=time.monotonic()-start,scope='actual stage diagnostic; no signed quadrature enclosure or final receiver certificate')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('work',type=Path);p.add_argument('--modes',type=int,default=4);p.add_argument('--ny',type=int,default=225);p.add_argument('--dt',type=float,default=.0006);p.add_argument('--budget',type=float,default=30);p.add_argument('--receiver',type=int,choices=(0,1),default=0);a=p.parse_args();assert 0<a.budget<=75;print(json.dumps(run(a.work,a.modes,a.ny,a.dt,a.budget,a.receiver)),flush=True)
