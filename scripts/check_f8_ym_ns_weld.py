"""F8 order-3 native spectral/phase weld, PR1527 123eff9.
NS pair-difference and SU2 orientation donors: master 116cd7d.
No physical equivalence, continuum convergence or nonlinear cascade claim.
"""
import numpy as np
import sympy as s
from scipy.linalg import eigh_tridiagonal
from scipy.integrate import quad
from itertools import combinations
from math import asinh,sqrt,ceil,log


def symbolic():
    eta=s.diag(-1,1,1,1,1);zero=s.zeros(5)
    def gen(i,j):
        a=s.zeros(5);a[i,j]=eta[j,j];a[j,i]=-eta[i,i];return a
    J=[-gen(2,3),-gen(3,1),-gen(1,2)]
    K=[gen(0,i) for i in (1,2,3)]
    comm=lambda a,b:a*b-b*a
    for A in J+K:assert A.T*eta+eta*A==zero
    for i in range(3):
        for j in range(3):
            R=sum((s.LeviCivita(i,j,k)*J[k] for k in range(3)),zero)
            B=sum((s.LeviCivita(i,j,k)*K[k] for k in range(3)),zero)
            assert comm(J[i],J[j])==R and comm(J[i],K[j])==B and comm(K[i],K[j])==-R
            assert comm(2*J[i],2*J[j])==4*R
    z=s.symbols('z',positive=True)
    # Poincare AdS5 spin connection: e^a=L dx^a/z, omega^a_4=-dx^a/z.
    A=[-gen(i,4)/z for i in range(4)]
    for i in range(4):
        assert A[i].T*eta+eta*A[i]==zero
        assert A[i].diff(z)==gen(i,4)/z**2
        for j in range(i+1,4):assert comm(A[i],A[j])==-gen(i,j)/z**2
    assert comm(K[0],K[1])!=J[2]
    # NS donor: divisionFreePairDifferenceCentering on coherent work.
    x=s.symbols('x:4',real=True);y=s.symbols('y:4',real=True);r=s.symbols('r:4',real=True)
    a=[x[i]+s.I*y[i] for i in range(4)];m=sum(a);w=[2*s.re(s.conjugate(m)*v) for v in a]
    assert s.expand(sum(w)-2*s.expand_complex(m*s.conjugate(m)))==0
    assert s.expand(-4*sum(r[i]*w[i] for i in range(4))+sum(r)*sum(w)+sum((r[i]-r[j])*(w[i]-w[j]) for i,j in combinations(range(4),2)))==0
    print('exact Lorentz brackets, SU2 normalization, AdS5 background curvature, NS coherent work PASS',flush=True)


def source(r,dr,eps):
    u=s.symbols('u',positive=True);f=s.exp(1-1/(1-u*u));d=[f]+[s.diff(f,u,n) for n in range(1,5)]
    p=[s.Rational(2,5)*(u*u*d[3]+2*u*d[2]-2*d[1]),s.Rational(4,7)*(u**4*d[3]-3*u**3*d[2]+3*u**2*d[1]),(u**6*d[3]-12*u**5*d[2]+75*u**4*d[1]-315*u**3*f)/35]
    targets=[s.Rational(2,5)*(u*u*d[4]+4*u*d[3]),s.Rational(4,7)*(u**4*d[4]+u**3*d[3]-6*u*u*d[2]+6*u*d[1]),(u**6*d[4]-6*u**5*d[3]+15*u**4*d[2]-15*u**3*d[1])/35]
    for i in range(3):assert s.simplify(p[i].diff(u)+(27*u*u*f if i==2 else 0)-targets[i])==0
    p=[s.lambdify(u,s.factor(v),'numpy') for v in p];out=np.zeros((3,len(r)))
    for j,x in enumerate(r):
        lo=max(0,x-dr/2);hi=min(eps,x+dr/2)
        if hi<=lo:continue
        a,b=lo/eps,hi/eps
        for q in range(3):
            dim=3+4*q;mass=(0 if b==1 else p[q](b))-(0 if a==0 else p[q](a))
            if q==2:mass+=quad(lambda u:27*u*u*np.exp(1-1/(1-u*u)),a,b)[0]
            out[q,j]=eps**dim*mass/(((x+dr/2)**dim-lo**dim)/dim)
    return out


def run(dr=.012,dy=.03,dt=.003,eps=.04,final=12.,pulse=.065):
    F=lambda t:asinh(t)-sqrt(1+t*t)/t
    T0=F(1);span=F(final)-T0;nt=ceil(span/dt);dt=span/nt
    n=ceil(3.2/dr);ny=ceil(2.1/dy)+1;r=np.arange(n)*dr;y=np.arange(ny)*dy
    rx=sqrt(span**2-(1-1/final)**2)-.012
    assert rx-eps-log(final)>dr/2 and dr<eps/3
    src=source(r,dr,eps);j=int(rx/dr);x=rx/dr-j
    w=np.array([-x*(x-1)*(x-2)/6,(x+1)*(x-1)*(x-2)/2,-(x+1)*x*(x-2)/2,(x+1)*x*(x-1)/6]);dw=np.array([-(3*x*x-6*x+2)/6,(3*x*x-4*x-1)/2,(-3*x*x+2*x+2)/2,(3*x*x-1)/6])/dr;dd=np.array([1-x,3*x-2,1-3*x,x])/dr**2
    geom=[];amps=[]
    for k in range(2*(nt+1)+1):
        T=T0+k*dt/2;t=max(1.,np.exp(T+1)/2)
        for _ in range(7):t=max(.5,t-(F(t)-T)/(sqrt(1+t*t)/t**2))
        v=-1/sqrt(1+t*t);b=1/t;geom.append((1+v,1-v,1.5/(b+y)[:,None]));ds=k*dt/2
        amps.append(-6*sqrt(1-v*v)/b*np.exp(1-1/(1-(2*ds/pulse-1)**2)) if 0<ds<pulse else 0.)
    def D(x):
        z=np.empty_like(x);z[0]=(x[1]-x[0])/dy;z[-1]=(x[-1]-x[-2])/dy;z[1:-1]=(x[2:]-x[:-2])/(2*dy);return z
    native=[];spectral=[];rate=[];hist=[]
    for q in range(3):
        d=3+4*q;ell=2*q;grid=np.arange(n,dtype=float);W=((grid+.5)**d-np.maximum(grid-.5,0)**d)/d;faces=(grid+.5)**(d-1)/dr**2
        diag=-(faces+np.r_[0.,faces[:-1]])/W;off=faces[:-1]/np.sqrt(W[:-1]*W[1:]);lam,V=eigh_tridiagonal(-diag,-off);root=np.sqrt(W/W.max());encode=lambda a:(a*root)@V
        assert lam.min()>0
        def R(U):
            z=U*diag;z[:,:-1]+=U[:,1:]*(faces[:-1]/W[:-1]);z[:,1:]+=U[:,:-1]*(faces[:-1]/W[1:]);return z
        def advance(spec):
            force_src=encode(src[q]) if spec else src[q];state=np.zeros((3,ny,n));save=[];series=[]
            def B(state,k):
                U,P,M=state;a,c,Z=geom[k];force=(-lam*U if spec else R(U))-Z*(P-M)
                p=a*D(P)+force;m=-c*D(M)+force;p[-1]-=2*a*P[-1]/dy;m[0]+=2*(a*P[0]-c*M[0]-2*amps[k]*force_src)/dy
                return state+dt*np.array([(a*P+c*M)/2,p,m])
            obs=(V[j-1:j+3,:].T@(w/root[j-1:j+3])) if spec else w
            for k in range(nt+2):
                U=state[0,0];series.append(U*obs if spec else np.dot(U[j-1:j+3],obs))
                if k>=nt-1:save.append(U.copy())
                if k==nt+1:break
                a=B(state,2*k);b=.75*state+.25*B(a,2*k+2);state=state/3+2*B(b,2*k+1)/3
            return np.array(save),np.array(series)
        raw,rs=advance(False);coeff,cs=advance(True);fac=(rx/eps)**ell;S=sqrt(1+final**2)/final
        tc=np.array([S*S/dt**2+1/(2*dt*final*sqrt(1+final**2)),-2*S*S/dt**2,S*S/dt**2-1/(2*dt*final*sqrt(1+final**2))]);hc=np.array([-S/dt,0,S/dt])
        def read(raw):
            t=tc@raw;h=hc@raw;u=raw[1];return np.array([-fac*(t@w+u@(dd+2*ell*dw/rx+ell*(ell-1)*w/rx**2))/(4*final**2),-fac*((t+h)@w-u@(dd+(2*ell+2)*dw/rx))/(2*final**2)])
        native.append(read(raw[:,j-1:j+3]));T=V[j-1:j+3,:].T/root[j-1:j+3];a=tc@coeff;h=hc@coeff;u=coeff[1]
        E4=-fac*(a*(T@w)+u*(T@(dd+2*ell*dw/rx+ell*(ell-1)*w/rx**2)))/(4*final**2)
        E5=-fac*((a+h)*(T@w)-u*(T@(dd+(2*ell+2)*dw/rx)))/(2*final**2)
        spectral.append(np.array([E4,E5]));rate.extend(lam);hist.append(fac*cs)
        err=np.max(np.abs(rs-cs.sum(axis=1)))/max(1e-30,np.max(np.abs(rs)));print('mode',ell,'history relative',err,'Weyl native',native[-1],'spectral',spectral[-1].sum(axis=1),flush=True);assert err<1e-7
    a=np.array(native);b=np.array([v.sum(axis=1) for v in spectral]);assert np.allclose(a,b,rtol=2e-5,atol=1e-8),(a,b)
    # Actual history Fourier amplitudes, not synthetic phase values.
    H=np.concatenate(hist,axis=1);A=np.fft.rfft(H,axis=0)[3];M=A.sum();work=2*np.real(M.conjugate()*A);rates=np.array(rate);N=len(A)
    lhs=-N*np.dot(rates,work)+rates.sum()*work.sum();rhs=-np.sum(np.triu((rates[:,None]-rates)*(work[:,None]-work),1));assert np.isclose(lhs,rhs,rtol=1e-9,atol=1e-8)
    assert np.isclose(work.sum(),2*abs(M)**2,rtol=1e-9);assert np.isclose(abs(M)**2,np.vdot(A,A).real+2*np.triu(np.outer(A.conj(),A),1).real.sum(),rtol=1e-9)
    print('grid',n,ny,nt,'both Weyl',a.sum(axis=0),b.sum(axis=0),'phase bin 3',abs(M)**2,'diagonal',np.vdot(A,A).real,'NS covariance',lhs,rhs,flush=True)
if __name__=='__main__':symbolic();run()
