"""Original F8 global auxiliary kernel and boundary-only numerical pilot.
Nodal kernel enclosures conditional on IEEE arithmetic; no continuous Volterra certificate.
"""
import json, math, sys, time
from fractions import Fraction as Q
from functools import lru_cache
import numpy as np
from scipy.optimize import brentq
from scipy.integrate import quad
from scipy.interpolate import CubicSpline
from scipy.special import roots_legendre
from scipy.linalg import solve as dense_solve
from numba import njit
import sympy as S
R=3.012; cut=1/13
up=lambda x:np.nextafter(x,np.inf)
dn=lambda x:np.nextafter(x,-np.inf)
@lru_cache(None)
def Fbox(b):
    D=2**96;x=1+b*b;n=math.isqrt((x*D*D).numerator//(x*D*D).denominator);l=Q(n,D);h=Q(n+1,D)
    def log(x):
        m=0
        while x>2:x/=2;m+=1
        def f(x):
            u=(x-1)/(x+1);v=sum(2*u**(2*j+1)/Q(2*j+1) for j in range(36));return v,v+2*u**73/(73*(1-u*u))
        a,c=f(x);d,e=f(Q(2));return a+m*d,c+m*e
    return log((1+l)/b)[0]-h,log((1+h)/b)[1]-l
F=lambda b:math.asinh(1/b)-math.sqrt(1+b*b)
def clock(n):
    a,c=Fbox(Q(1,12));l,r=Fbox(Q(1));span=(a-r,c-l);dt=up(float(span[1]/n));assert Q(float(dt))*n>=span[1]
    t=np.arange(n+1)*dt;b=np.array([brentq(lambda x:F(x)-F(1/12)+v,.07,1.1,xtol=1e-14) for v in t]);lo=[];hi=[]
    for i,x in enumerate(b):
        bl=Q(math.floor(x*10**12)-2,10**12);bh=Q(math.ceil(x*10**12)+2,10**12);v=i*Q(float(dt));assert Fbox(bl)[0]>=c-v and Fbox(bh)[1]<=a-v;lo.append(dn(float(bl)));hi.append(up(float(bh)))
    return dt,t,b,np.array(lo),np.array(hi),float(sum(span)/2)
@njit(cache=True)
def grid(xi,k,h,na,nb):
    r=np.ones((na+1,nb+1));d=h*h/16
    for i in range(1,na+1):
        for j in range(1,nb+1):
            z=max(1/13,xi+(i-j)*h/2);q=d*(k*k+3.75/z**2);a=r[i-1,j];b=r[i,j-1];c=r[i-1,j-1];r[i,j]=((1-q)*(a+b)-(1+q)*c)/(1+q)
    return r
@njit(cache=True)
def derivatives(r,xi,k,h):
    a=np.zeros_like(r);b=np.zeros_like(r)
    for i in range(r.shape[0]):
        for j in range(r.shape[1]):
            z=max(1/13,xi+(i-j)*h/2);q=(k*k+3.75/z**2)*r[i,j]
            if j:
                z=max(1/13,xi+(i-j+1)*h/2);a[i,j]=a[i,j-1]-h*(q+(k*k+3.75/z**2)*r[i,j-1])/8
            if i:
                z=max(1/13,xi+(i-j-1)*h/2);b[i,j]=b[i-1,j]-h*(q+(k*k+3.75/z**2)*r[i-1,j])/8
    return a,b

def interp(r,A,B,h):
    i=(A/h).astype(int);j=(B/h).astype(int);x=A/h-i;y=B/h-j;a=r[i,j];b=r[i+1,j];c=r[i,j+1];d=r[i+1,j+1];da=((1-y)*(b-a)+y*(d-c))/h;db=((1-x)*(c-a)+x*(d-b))/h
    return ((1-x)*(1-y)*a+x*(1-y)*b+(1-x)*y*c+x*y*d)/2,(da+db)/2,(da-db)/2

def certify(r,xi_l,xi_h,mode,h,A,B,eps):
    # dyadic h, literal binary nodes. Entire cell residual of continuous bilinear R_h.
    a,b,c,d=r[:-1,:-1],r[1:,:-1],r[:-1,1:],r[1:,1:];x=np.arange(a.shape[0],dtype=float)[:,None];y=np.arange(a.shape[1],dtype=float)[None,:]
    zl=np.maximum(dn(cut),dn(xi_l+(x-y-1)*h/2));zh=np.maximum(up(cut),up(xi_h+(x-y+1)*h/2))
    kl=dn(float(Q(mode)*Q(333,106)/Q('3.012')));kh=up(float(Q(mode)*Q(355,113)/Q('3.012')))
    vl=dn(dn(kl*kl)+dn(3.75/up(zh*zh)));vh=up(up(kh*kh)+up(3.75/dn(zl*zl)))
    cl=dn(dn(dn(d-b)-c)+a)*4/h**2;ch=up(up(up(d-b)-c)+a)*4/h**2
    l=np.minimum(np.minimum(a,b),np.minimum(c,d));u=np.maximum(np.maximum(a,b),np.maximum(c,d));pl=dn(np.minimum(np.minimum(vl*l,vl*u),np.minimum(vh*l,vh*u)));ph=up(np.maximum(np.maximum(vl*l,vl*u),np.maximum(vh*l,vh*u)))
    res=np.maximum(abs(dn(cl+pl)),abs(up(ch+ph)));q=up(up(res*res)*h*h)
    for i in range(1,len(q)):q[i]=up(q[i]+q[i-1])
    for j in range(1,q.shape[1]):q[:,j]=up(q[:,j]+q[:,j-1])
    fm=np.maximum.accumulate(np.maximum.accumulate(res,0),1);vm=np.maximum.accumulate(np.maximum.accumulate(vh,0),1)
    out=[]
    for aa,bb,ee in zip(A,B,eps):
        al=max(0,int(np.floor(dn(aa-ee)/h)));ah=int(np.floor(up(aa+ee)/h));bl=max(0,int(np.floor(dn(bb-ee)/h)));bh=int(np.floor(up(bb+ee)/h));T=up(up(up(aa+ee)+up(bb+ee))/2)
        err=up(T*up(np.sqrt(up(q[ah,bh]/2))));fac=up(fm[ah,bh]+up(vm[ah,bh]*err));er=up(up(up(aa+ee)+up(bb+ee))*fac/8)
        block=r[al:ah+2,bl:bh+2];da=block[1:,:]-block[:-1,:];db=block[:,1:]-block[:,:-1];dl=dn(np.min(da))/h;du=up(np.max(da))/h;el=dn(np.min(db))/h;eu=up(np.max(db))/h
        out.append([dn(np.min(block)/2-up(err/2)),up(np.max(block)/2+up(err/2)),dn(dn((dl+el)/2)-er),up(up((du+eu)/2)+er),dn(dn((dl-eu)/2)-er),up(up((du-el)/2)+er)])
    return np.array(out),float(np.max(res))

def kernels(t,b,lo,hi,dt,h,mode,cert):
    n=len(b);k=mode*np.pi/R;K=np.zeros((n,n));Kt=K.copy();Kz=K.copy();bounds=np.zeros((n,n,6));maxres=0
    for j in range(n):
        ix=np.r_[np.arange(j),np.arange(j+1,n)];lag=abs(ix-j)*dt;dz=b[ix]-b[j];A=lag+dz;B=lag-dz;ee=up(up(np.maximum(b[ix]-lo[ix],hi[ix]-b[ix]))+up(max(b[j]-lo[j],hi[j]-b[j]))+1e-13);assert n<=513 and min(A-ee)>0 and min(B-ee)>0
        r=grid(b[j],k,h,int(np.ceil(max(A+ee)/h))+2,int(np.ceil(max(B+ee)/h))+2);K[ix,j]=interp(r,A,B,h)[0];ra,rb=derivatives(r,b[j],k,h);da=interp(ra,A,B,h)[0];db=interp(rb,A,B,h)[0];Kt[ix,j]=da+db;Kz[ix,j]=da-db
        if cert:bounds[ix,j],res=certify(r,lo[j],hi[j],mode,h,A,B,ee);maxres=max(maxres,res)
    np.fill_diagonal(K,.5);Kx=Kz.T.copy()
    if cert:
        for m in (0,1):np.fill_diagonal(bounds[:,:,m],.5)
        assert np.all(bounds[:,:,0]<=bounds[:,:,1].T) and np.all(bounds[:,:,0].T<=bounds[:,:,1]),'reciprocal kernel enclosures disagree'
        widths=np.max(bounds[:,:,1::2]-bounds[:,:,::2],axis=(0,1)).tolist()
    else:widths=None
    return K,Kt,Kx,dict(full_pair=[K[-1,0],Kt[-1,0],Kx[-1,0]],full_pair_bounds=[bounds[-1,0,:2].tolist(),bounds[-1,0,2:4].tolist(),bounds[0,-1,4:6].tolist()] if cert else None,max_cell_residual=maxres,max_nodal_widths=widths,reciprocity=float(np.max(abs(K-K.T))))

def solve(t,b,dt,mode,receiver,K,Kt,Kx,span):
    k=mode*np.pi/R;u=b/np.sqrt(1+b*b);a=b/(1+b*b)**2;s=1-u*u;den=1+u*u;d=u*(3+u*u)/den;e=s/den;C=(1+u)**2/(2*den)
    q=10*(.15-t);chi=np.zeros_like(q);mask=abs(q)<1;norm=.1*quad(lambda q:math.exp(1-1/(1-q*q)),-1,1)[0];chi[mask]=np.exp(1-1/(1-q[mask]**2))/norm;sc,extra,sign=((.25,0,-1),(.5,2,1))[receiver];beta=np.sqrt(1+b*b);A2=-sc*b*b*beta**2*chi;A1=-sc*b*b*(-b*b/beta+extra*beta)*chi;A0=sign*sc*b*b*chi
    B,T=S.symbols('b tau',positive=True);U=B/S.sqrt(1+B*B);D=1+U*U;c0=(B/(1+B*B)**2-3*U*U/B)*B**(-S.Rational(3,2))/D;c1=U*k*k*B**(-S.Rational(3,2))/D
    c0,c1,c0p,c1p=S.lambdify(B,(c0,c1,U*S.diff(c0,B),U*S.diff(c1,B)),'numpy',cse=True)(b);hf=-b**1.5*c0-1.5/b;hm=b**1.5;hs=b**1.5*s*A2
    n=len(b);E=np.zeros((n,2,3));f=np.zeros((n,2));E[:,0,0]=s*c1+u*c0*hf+u*k*k*b**-1.5+c0p;E[:,0,1]=u*c0*hm;E[:,0,2]=-s;E[:,1,0]=u*c1*hf+c1p;E[:,1,1]=u*c1*hm;f[:,0]=s*A1+2*u*a*A2+u*c0*hs;f[:,1]=k*k*A0+u*c1*hs
    X=np.zeros((n,3));res=0;matall=np.eye(3*n)
    for i in range(1,n):
        j=slice(0,i+1);L=np.zeros((i+1,3,3));g=np.zeros((i+1,3));L[:,0,0]=(2*a[j]*s[j]/den[j]**2*K[i,j]-d[j]*Kt[i,j]+(1+3*u[j]**2)/den[j]*Kx[i,j]-e[j]*K[i,j]*hf[j])/C[i];L[:,0,1]=-e[j]*K[i,j]*hm[j]/C[i];g[:,0]=-e[j]*K[i,j]*hs[j]/C[i];L[:,1:,:]=E[j];g[:,1:]=f[j];w=np.full(i+1,dt);w[[0,-1]]=dt/2;rhs=np.einsum('j,jab,jb->a',w[:-1],L[:-1],X[:i])+w@g;mat=np.eye(3)-w[-1]*L[-1];X[i]=np.linalg.solve(mat,rhs);res=max(res,np.max(abs(mat@X[i]-rhs)));matall[3*i:3*i+3,:3*(i+1)]-=np.transpose(w[:,None,None]*L,(1,0,2)).reshape(3,-1)
    F0=X[:,0];J1=X[:,2]-c1*F0;hw=hf*F0+hm*X[:,1]+hs
    q=2*(span-T)/.065-1;g=-6/(B*S.sqrt(1+B*B))*S.exp(1-1/(1-q*q));der=lambda p:S.diff(p,T)+U*S.diff(p,B);Cs=B**S.Rational(3,2)*der(B**-3*g)/D;fun=S.lambdify((B,T),(g,Cs,der(Cs)),'numpy',cse=True);g0=np.zeros(n);cs=g0.copy();csp=g0.copy();mask=(t>span-.065)&(t<span);g0[mask],cs[mask],csp[mask]=fun(b[mask],t[mask]);coef=math.sqrt(2/R)*.04**4*quad(lambda r:r*math.sin(k*r)*math.exp(1-1/(1-(r/.04)**2)),0,.04,epsabs=1e-18)[0]
    xx,ww=roots_legendre(128);ts=span-.065*(1+xx)/2;bs=CubicSpline(t,b)(ts);us=bs/np.sqrt(1+bs*bs);gs,css,csps=fun(bs,ts);ff=CubicSpline(t,F0);hh=CubicSpline(t,hw)(ts);jj=CubicSpline(t,J1)(ts)
    o=coef*.065/2*np.dot(ww,csps*ff(ts)+us*css*hh+us*gs*jj);o1=coef*.065/2*np.dot(ww,-css*ff(ts,1)+us*css*hh+us*gs*jj)
    # Signed finite inverse certificate for literal binary64 collocation matrix.
    # Standard dot-product error bound (IEEE round-to-nearest, no overflow;
    # additive conservative subnormal budget). This is NOT a continuous inverse.
    inverse=dense_solve(matall,np.eye(3*n),check_finite=True);m=3*n;eps=2.**-53;gamma=up(2*m*eps/(1-2*m*eps))
    def norm(A):
        # exact nonnegative row sums enclosed using positive floating summation bound
        return up(np.max(np.sum(abs(A),axis=1))/(1-gamma)+m*1e-300)
    p=matall@inverse;E=np.eye(m)-p;rho=up(2*(norm(E)+up(gamma*up(norm(matall)*norm(inverse)))+up(eps*(1+norm(p)))+1e-290))
    invnorm=up(norm(inverse)/dn(1-rho)) if rho<1 else None
    return dict(receiver=receiver,finite_inverse_upper=invnorm,finite_inverse_defect=rho,observation=float(o),first_derivative_observation=float(o1),nodal_observation=float(coef*np.trapezoid(csp*F0+u*cs*hw+u*g0*J1,dx=dt)),max_history=np.max(abs(X),axis=0).tolist(),linear_residual=float(res))

def run(n,cert):
    assert n in (64,128,256,512)
    start=time.monotonic();dt,t,b,lo,hi,span=clock(n);h=1/(2*min(n,256));rows=[];print('clock',n,time.monotonic()-start,flush=True)
    for mode in (1,2):
        K,Kt,Kx,rec=kernels(t,b,lo,hi,dt,h,mode,cert);print('kernel',mode,rec,flush=True);rows.append(dict(mode=mode,kernel=rec,receivers=[solve(t,b,dt,mode,r,K,Kt,Kx,span) for r in (0,1)]))
    return dict(n=n,dt=dt,characteristic_h=h,seconds=time.monotonic()-start,certified_kernel_nodes=cert,rows=rows,scope='conditional nodal kernel bounds, numerical Volterra and source quadrature only; no continuous receiver certificate')
def symbolic():
    A,B,t,z,x,h,a,b,c,d,q=S.symbols('A B t z x h a b c d q');r=S.Function('r')(A,B);f=r.subs({A:t+z-x,B:t-z+x},simultaneous=True)
    assert S.simplify(S.diff(f,t,2)-S.diff(f,z,2)-4*S.diff(r,A,B).subs({A:t+z-x,B:t-z+x},simultaneous=True))==0
    p=(1-A/h)*(1-B/h)*a+A/h*(1-B/h)*b+(1-A/h)*B/h*c+A*B*d/h**2
    assert S.simplify(S.diff(p,A,B)-(d-b-c+a)/h**2)==0
    assert S.simplify(d-b-c+a+q*(a+b+c+d)-((1+q)*d-(1-q)*(b+c)+(1+q)*a))==0
    # constant-potential Riemann coefficient recurrence for J0(sqrt(V A B))
    n=S.symbols('n',integer=True,nonnegative=True);v=S.symbols('V');c=(-v/4)**n/S.factorial(n)**2
    assert S.simplify(4*(n+1)**2*c.subs(n,n+1)+v*c)==0
    return 4
if __name__=='__main__':print(json.dumps(dict(symbolic_checks=symbolic(),**run(int(sys.argv[1]),'--cert' in sys.argv)),indent=2),flush=True)
