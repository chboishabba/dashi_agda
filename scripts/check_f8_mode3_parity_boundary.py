"""Original F8 mode3 two-parity boundary expansion and independent receiver.
Exact symbolic checks; source-clock single-mode transfer diagnostics only.
No production or native proof-kernel claim.
"""
import json, math
from fractions import Fraction as Q
import sympy as S
import numpy as np


def parity_jet(U,W,h):
    """Normal index first; original state only, no SAT projection."""
    if len(U)<5 or len(W)<5 or (not isinstance(h,S.Basic) and h<=0):raise ValueError('five normal rows required')
    raw=((-3*U[0]+4*U[1]-U[2])/(2*h),(-3*W[0]+4*W[1]-W[2])/(2*h),(U[2]-2*U[1]+U[0])/h**2)
    even=((U[2]-U[0])/(2*h),(W[2]-W[0])/(2*h),(U[4]-2*U[2]+U[0])/(4*h**2))
    return raw,even,tuple(x-y for x,y in zip(raw,even))


def exact():
    checks=0
    def eq(a,b=0):
        nonlocal checks
        assert S.simplify(a-b)==0,(a,b)
        checks+=1
    h,a,c,sg=S.symbols('h a c sg',nonzero=True)
    p2,p3,m2,m3,Ap,Am,Bp,Bm,Cp,Cm,Dp,Dm=S.symbols('p2 p3 m2 m3 Ap Am Bp Bm Cp Cm Dp Dm')
    # Taylor residual after smooth/reversed interior PDE cancellation.
    # The derivative of the h^2 oscillatory component at the lower wall
    # is -2h B - h^2 B_y; at the upper wall it is +2 sg h B - sg h^2 B_y.
    for sign in (1,-1):
        lowP=a*(p2/2-2*Bp);lowM=-c*m2/2+2*c*Bm+2*(a*(Ap+Bp)-c*(Am+Bm))
        topP=-a*p2/2+2*sign*a*Bp-2*a*(Ap+sign*Bp);topM=c*m2/2-2*sign*c*Bm
        eq(lowP.subs(Bp,p2/4));eq(lowM.subs({Bp:p2/4,Am:(a*Ap+a*p2/4-c*m2/4)/c}))
        eq(topP.subs(Ap,-p2/4));eq(topM.subs(Bm,sign*m2/4))
        lowP3=a*(p3/6-2*Dp);lowM3=-c*m3/6+2*c*Dm+2*(a*(Cp+Dp)-c*(Cm+Dm))
        topP3=a*p3/6+2*sign*a*Dp-2*a*(Cp+sign*Dp);topM3=-c*m3/6-2*sign*c*Dm
        eq(lowP3.subs(Dp,p3/12));eq(lowM3.subs({Dp:p3/12,Cm:(a*Cp+a*p3/12-c*m3/12)/c}))
        eq(topP3.subs(Cp,p3/12));eq(topM3.subs(Dm,-sign*m3/12))
    # Independent exact Taylor expansion of D, including reversed parity.
    x=S.symbols('x:5');b=S.symbols('b:5');A=S.symbols('A:5');d=S.symbols('d:5');C=S.symbols('C:5')
    def series(j,sg):
        poly=lambda z:sum(z[k]*(j*h)**k/S.factorial(k) for k in range(5))
        return poly(x)+h*h*(poly(A)+sg*poly(b))+h**3*(poly(C)+sg*poly(d))
    def coeff(expr,k):return S.expand(expr).coeff(h,k)
    left=(series(1,-1)-series(0,1))/h;right=(series(0,sg)-series(-1,-sg))/h
    center=(series(1,-sg)-series(-1,-sg))/(2*h)
    for expr,expected in ((left,[x[1],x[2]/2-2*b[0],x[3]/6+A[1]-b[1]-2*d[0]]),(right,[x[1],-x[2]/2+2*sg*b[0],x[3]/6+A[1]-sg*b[1]+2*sg*d[0]]),(center,[x[1],0,x[3]/6+A[1]-sg*b[1]])):
        for k,val in enumerate(expected):eq(coeff(expr,k),val)
    U=[series(j,(-1)**j) for j in range(5)]
    raw,even,delta=parity_jet(U,U,h)
    eq(coeff(raw[2],0),x[2]+4*b[0]);eq(coeff(even[2],0),x[2]);eq(coeff(delta[2],0),4*b[0]);eq(coeff(raw[0],0),x[1]);eq(coeff(even[0],0),x[1])
    # Exact five-row constraint-to-stage correspondence, no boundary Q=0.
    u0,u1,n1,n3,w0,w1,nt1,nt3=S.symbols('u0 u1 n1 n3 w0 w1 nt1 nt3')
    U=[u0,u1,u0+2*h*n1,S.Symbol('u3'),u0+2*h*(n1+n3)]
    W=[w0,w1,w0+2*h*nt1,S.Symbol('w3'),w0+2*h*(nt1+nt3)]
    r,e,dd=parity_jet(U,W,h)
    eq(e[0],n1);eq(e[1],nt1);eq(e[2],(n3-n1)/(2*h));eq(dd[2],(3*U[0]-8*U[1]+6*U[2]-U[4])/(4*h*h))
    P1,P3,M1,M3,F=S.symbols('P1 P3 M1 M3 F')
    pt=a*(P3-P1)/(2*h)+F;mt=-c*(M3-M1)/(2*h)+F
    eq((pt-F)/(2*a)+(mt-F)/(2*c),((P3-M3)-(P1-M1))/(4*h))
    # Original direct geometric electric Weyl coefficient of normal jets.
    b0,v,acc,Wt,D,E,Y,L,W0=S.symbols('b0 v acc Wt D E Y L W0');s=1-v*v
    box=-Wt+2*v*E+s*Y+acc*D+L;N=v*v*Wt+2*v*s*E+s*s*Y-v*v*acc*D
    direct=b0*b0*(-N/(2*s)+box/6)
    eq(S.diff(direct,D),b0*b0*acc*(v*v/(2*s)+S.Rational(1,6)))
    eq(S.diff(direct,E),-2*b0*b0*v/3);eq(S.diff(direct,Y),-b0*b0*s/3)
    eq(direct.subs(Y,Y+4*b[0])-direct,-4*b0*b0*s*b[0]/3)
    # For a smooth quadratic on even rows, the independent parity stencil is exact.
    U=[Q(j*j,100) for j in range(5)];r,e,d=parity_jet(U,U,Q(1,10));eq(e[2],2);eq(d[2])
    # Alternating branch has reversed moving shift but the same wave cone.
    U=S.Function('U');T,y=S.symbols('T y');v=S.Function('v')(T);N=-S.diff(U(T,y),y);W=S.diff(U(T,y),T);a,c=1+v,1-v
    P=W+c*N;M=W-a*N
    eq(S.diff(v,T)*N+(-a*a*S.diff(P,y)+c*c*S.diff(M,y))/2,-2*v*S.diff(W,y)+(1-v*v)*S.diff(U(T,y),y,2)-S.diff(v,T)*S.diff(U(T,y),y))
    w=S.symbols('w',real=True);f=S.sqrt(1-w*w)
    eq(S.diff(f,w,2),-1/(1-w*w)**S.Rational(3,2))
    return checks


def modal_diagnostics():
    """Literal mode3 normal stage on one fixed radial eigenmode K=k^2.
    Actual original clock, pulse, wall/top SAT. Unit modal source amplitude;
    NOT the three-channel FV spatial source or a full physical receiver run.
    """
    from numba import njit
    @njit
    def clock(t):return np.arcsinh(t)-np.sqrt(1+t*t)/t
    @njit
    def coef(T):
        t=max(1.,np.exp(T+1)/2)
        for _ in range(9):t=max(.5,t-(clock(t)-T)/(np.sqrt(1+t*t)/t**2))
        b=1/t;v=-1/np.sqrt(1+t*t);ds=T-clock(1.)
        q=2*ds/.065-1
        amp=-6*np.sqrt(1-v*v)/b*np.exp(1-1/(1-q*q)) if 0<ds<.065 else 0.
        return b,v,amp
    @njit
    def rhs(X,Y,h,k,T):
        b,v,G=coef(T);a=1+v;c=1-v;n=X.shape[1]
        for j in range(n):
            u,p,m=X[0,j],X[1,j],X[2,j]
            if j==0:dp=(X[1,1]-p)/h;dm=(X[2,1]-m)/h
            elif j==n-1:dp=(p-X[1,j-1])/h;dm=(m-X[2,j-1])/h
            else:dp=(X[1,j+1]-X[1,j-1])/(2*h);dm=(X[2,j+1]-X[2,j-1])/(2*h)
            F=-k*k*u-3*(p-m)/(2*(b+j*h))
            Y[0,j]=(a*p+c*m)/2;Y[1,j]=a*dp+F;Y[2,j]=-c*dm+F
            if j==0:Y[2,j]+=2*(a*p-c*m-2*G)/h
            if j==n-1:Y[1,j]-=2*a*p/h
    @njit
    def evolve(n,k):
        h=2.01/n;T0=clock(1.);T1=clock(12.);steps=int(np.ceil((T1-T0)*(k+10/h+400)/.9));dt=(T1-T0)/steps
        X=np.zeros((3,n+1));Y=X.copy();A=X.copy();B=X.copy()
        for i in range(steps):
            T=T0+i*dt
            rhs(X,Y,h,k,T);A[:]=X+dt*Y
            rhs(A,Y,h,k,T+dt);B[:]=.75*X+.25*(A+dt*Y)
            rhs(B,Y,h,k,T+dt/2);X[:]=(X+2*(B+dt*Y))/3
        rhs(X,Y,h,k,T1)
        return X,Y,dt,steps
    rows=[]
    for k in (1.,3.):
        for n in (128,256,512,1024,2048):
            X,Y,dt,steps=evolve(n,k);h=2.01/n;b=1/12;v=-1/math.sqrt(145);a=1+v;c=1-v
            U,P,M=X;W,Pt,Mt=Y;N=(P-M)/2;Nt=(Pt-Mt)/2
            r,e,d=parity_jet(U,W,h);F=-k*k*U[2]-3*N[2]/(b+2*h)
            np.testing.assert_allclose(e,(N[1],Nt[1],(Pt[2]-F)/(2*a)+(Mt[2]-F)/(2*c)),rtol=1e-7,atol=1e-7)
            rows.append(dict(k=k,N=n,dt=dt,steps=steps,U0=float(U[0]),raw_Y=float(r[2]),even_Y=float(e[2]),raw_minus_even_Y=float(d[2]),raw_minus_even_direct=float(b*b*((b/(1+b*b)**2)*(v*v/(2*(1-v*v))+1/6)*d[0]-2*v*d[1]/3-(1-v*v)*d[2]/3)),interior_Q_max=float(np.max(abs(N[1:-1]-(U[2:]-U[:-2])/(2*h))))))
    return rows

if __name__=='__main__':
    print(json.dumps(dict(exact_checks=exact(),modal_diagnostics=modal_diagnostics(),scope='exact algebra and normalized single radial-mode source-clock diagnostics; fixed radial operator asymptotic argument in roadmap; no full production or kernel proof'),indent=2))
