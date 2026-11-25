"""Original F8 forward scalar trace, finite transpose and continuum comparison.
Uses prior auxiliary global kernel. No continuous inverse certificate claimed.
"""
import json,sys,time,math
import numpy as np
import sympy as S
from scipy.interpolate import CubicSpline
from scipy.special import roots_legendre
from scipy.integrate import quad
from scipy.linalg import solve_triangular
from check_f8_global_wall_kernel import clock,kernels,R


def symbolic():
    v,a,F,Fp,h,Pt,Pz=S.symbols('v a F Fp h Pt Pz',real=True);s=1-v*v
    checks=[]
    def eq(name,x,y):
        assert S.simplify(x-y)==0,name;checks.append(name)
    eq('physical wall tangent', (Pt+v*Pz).subs({Pt:(Fp-v*h)/s,Pz:(h-v*Fp)/s}),Fp)
    eq('physical wall flux', (Pz+v*Pt).subs({Pt:(Fp-v*h)/s,Pz:(h-v*Fp)/s}),h)
    eq('single layer',-a*F-2*v*Pt-(1+v*v)*Pz,-a*F-v*(Pt+v*Pz)-(Pz+v*Pt))
    eq('diagonal',1-s/(2*(1-v))+v/2,S.Rational(1,2))
    eq('normal history coefficient',v*v+s,1)
    t,r=S.symbols('t r',real=True);b=1-r/4+r*r/20;u=S.diff(b,r);f=(r-b+1)**3;g=(u-1)*3*(r-b+1)**2
    eq('free accelerating wall',S.diff(f,r)/2,-g/2)
    eq('free initial',f.subs(r,0),0)
    return checks


def forward(t,b,dt,mode,K,Kt,Kx,span):
    # Input matrices on ascending reverse clock; flip both axes for forward time.
    b=b[::-1].copy();K=K[::-1,::-1];Kt=Kt[::-1,::-1];Kx=Kx[::-1,::-1];v=-b/np.sqrt(1+b*b);k=mode*np.pi/R;n=len(t)
    L=2*(Kx-Kt*v[None,:]+1.5*K/b[None,:]);A=np.eye(n);rhs=np.zeros(n);rhsnod=np.zeros(n)
    B,T=S.symbols('b T',positive=True);V=-B/S.sqrt(1+B*B);beta=S.sqrt(1+B*B);q=2*T/.065-1
    g=-6/(B*beta)*S.exp(1-1/(1-q*q));gf=S.lambdify((B,T),g,'numpy');bs=CubicSpline(t,b)
    coef=math.sqrt(2/R)*.04**4*quad(lambda r:r*math.sin(k*r)*math.exp(1-1/(1-(r/.04)**2)),0,.04,epsabs=1e-24)[0]
    gs=np.zeros(n);mask=(t>0)&(t<.065);gs[mask]=gf(b[mask],t[mask])*coef/b[mask]**1.5
    x,w=roots_legendre(96)
    for i in range(1,n):
        wt=np.full(i+1,dt);wt[[0,-1]]=dt/2;A[i,:i+1]-=wt*L[i,:i+1]
        rhsnod[i]=-2*np.dot(wt,K[i,:i+1]*gs[:i+1])
        end=min(t[i],.065);ts=(x+1)*end/2;bb=bs(ts);kk=CubicSpline(t[:i+1],K[i,:i+1])(ts)
        rhs[i]=-end*coef*np.dot(w,kk*gf(bb,ts)/bb**1.5)
    F=solve_triangular(A,rhs,lower=True);Fn=solve_triangular(A,rhsnod,lower=True)
    # Same original continuous q as prior reverse solver. Independent quadrature
    # of cubic spline trace; its evaluation is a linear functional on nodal F.
    wq=10*(T-span+.15);chi=S.exp(1-1/(1-wq*wq));D=lambda a:S.diff(a,T)+V*S.diff(a,B)
    norm=.1*quad(lambda x:math.exp(1-1/(1-x*x)),-1,1,epsabs=1e-13)[0]
    ts=span-.15+.1*x;bb=bs(ts);basis=CubicSpline(t,np.eye(n),axis=0)(ts);rows=[]
    for receiver,(scale,extra,sign) in enumerate(((S.Rational(1,4),0,-1),(S.Rational(1,2),2,1))):
        a2=-scale*B**2*beta**2*chi/norm;a1=-scale*B**2*(-B**2/beta+extra*beta)*chi/norm;a0=sign*scale*B**2*chi/norm
        qf=S.lambdify((B,T),D(D(a2))-D(a1)-k*k*a0,'numpy',cse=True);qq=.1*w*qf(bb,ts)*bb**1.5;ell=qq@basis
        lam=solve_triangular(A.T,ell,lower=False);o=ell@F;ot=lam@rhs;on=ell@Fn
        rows.append(dict(receiver=receiver,forward=float(o),finite_transpose=float(ot),transpose_discrepancy=float(abs(o-ot)),nodal_source=float(on),forward_residual=float(np.max(abs(A@F-rhs))),transpose_residual=float(np.max(abs(A.T@lam-ell))),max_trace=float(np.max(abs(F)))))
    return rows


def run(n):
    start=time.monotonic();dt,t,b,lo,hi,span=clock(n);h=1/(2*min(n,256));rows=[]
    for mode in (1,2):
        K,Kt,Kx,rec=kernels(t,b,lo,hi,dt,h,mode,False);r=forward(t,b,dt,mode,K,Kt,Kx,span);rows.append(dict(mode=mode,receivers=r));print(json.dumps(rows[-1]),flush=True)
    return dict(n=n,h=h,seconds=time.monotonic()-start,checks=symbolic(),rows=rows,scope='forward scalar continuous equation, numerical kernel/collocation and source/receiver quadrature; finite transpose diagnostic only')
if __name__=='__main__':print(json.dumps(run(int(sys.argv[1])),indent=2),flush=True)
