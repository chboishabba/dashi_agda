"""Expanded radial/tangential compact material trial spaces on the original TOV slice.
Fixed conformal background; exact exterior scalar DtN; finite trial matrix only.
"""
import numpy as np
import sympy as s
from scipy.integrate import cumulative_trapezoid
from scipy.sparse import coo_matrix, diags
from scipy.sparse.linalg import spsolve
from numpy.polynomial.legendre import Legendre, leggauss
from check_tov_polar_conformal_trial import coefficients

def material():
    x=s.symbols('x'); l=s.Rational(1,10); p=l/(8*s.pi)
    rho=(2+l)*p*(1-x); pr=-p*(1-x)**2
    f=1-l*(2+l)*(x/3-x*x/5)
    P=(2+l)*(s.Rational(1,3)-x/5)/2-(1-x)**2/2
    pt=pr+x*s.diff(pr,x)+x*l*(rho+pr)*P/(2*f)
    a=(rho+pt)/2; d=(rho+pr)/(2*f); b=s.cancel((d-a)/x); V=rho-2*a-d*f
    return s.lambdify(x,[s.diff(q,x,j) for q in (a,b,V) for j in range(3)],'numpy')

def run(n,ell,degree=1,annulus=(.15,.85)):
    L=ell*(ell+1); M=7/500; coef=coefficients(); nodes=np.linspace(0,1,n+1)
    t,wt=leggauss(6); dr=1/n
    r=(nodes[:-1,None]+dr*(t+1)/2).ravel(); wq=np.tile(dr*wt/2,n)
    f,V,_,c,*_=coef(r)
    rr=np.linspace(0,1,20001); nu=cumulative_trapezoid(coef(np.maximum(rr,1e-9))[-1],rr,initial=0)
    N=np.sqrt(1-2*M)*np.exp(np.interp(r,rr,nu)-nu[-1]); w=r*r/np.sqrt(f); A=r*r*np.sqrt(f)
    mu,aw=leggauss(2*ell+8); Y=Legendre.basis(ell)*np.sqrt((2*ell+1)/2)
    H=Y(mu); D=-np.sqrt(1-mu*mu)*Y.deriv()(mu)
    DD=(1-mu*mu)*Y.deriv(2)(mu)-mu*Y.deriv()(mu); TT=-mu*Y.deriv()(mu)
    assert abs(np.sum(aw*H*H)-1)<1e-12
    assert abs(np.sum(aw*D*D)-L)<1e-10
    # Angular measure includes azimuth normalization in the harmonic.
    shape=np.array([(1-t)/2,(1+t)/2]); rows=[];cols=[];vals=[]
    for i in range(2):
        for j in range(2):
            v=wq*N*N*(A*(2*i-1)*(2*j-1)/dr**2+w*L/r**2*np.tile(shape[i]*shape[j],n))
            vals.extend(v.reshape(n,-1).sum(axis=1));rows.extend(np.arange(n)+i);cols.extend(np.arange(n)+j)
    R=(1-M+np.sqrt(1-2*M))/2; z=M/(2*R)
    dtn=np.zeros(n+1);dtn[-1]=(1-2*M)*(ell+1+z/(1-z))
    K=coo_matrix((vals,(rows,cols)),shape=(n+1,n+1)).tocsr()+diags(dtn)
    # Matrix jets of material action in local orthonormal spatial frame.
    a,aa,aaa,b,bb,bbb,V,Vp,Vpp=[np.asarray(q)[:,None,None,None] for q in material()(r*r)]
    r0=r[:,None]; f0=f[:,None]; I=np.eye(3); y=np.zeros((len(r),1,3,1));y[...,0,0]=r0
    B0=np.zeros((len(r),1,3,3));B0[...,0,0]=f0;B0[...,1,1]=B0[...,2,2]=1
    E=np.zeros_like(B0); E[...,0,0]=np.sqrt(f0); E[...,1,1]=E[...,2,2]=1
    tr=lambda x:np.trace(x,axis1=-2,axis2=-1)
    T=lambda x:np.swapaxes(x,-1,-2)
    lo,hi=annulus
    q=(r-lo)*(hi-r); p=np.maximum(q,0)**3*1000
    dp=np.where(q>0,3000*q*q*(lo+hi-2*r),0)
    x=2*(r-lo)/(hi-lo)-1
    P=np.array([p*Legendre.basis(k)(x) for k in range(degree)])
    DP=np.array([dp*Legendre.basis(k)(x)+p*Legendre.basis(k).deriv()(x)*2/(hi-lo) for k in range(degree)])
    def energy(u,v):
        U,Up=u@P,u@DP; W,Wp=v@P,v@DP
        Z=np.zeros((len(r),len(mu),3,1));Z[...,0,0]=U[:,None]*H;Z[...,1,0]=W[:,None]*D
        J=np.zeros((len(r),len(mu),3,3))
        J[...,0,0]=np.sqrt(f0)*Up[:,None]*H
        J[...,1,0]=np.sqrt(f0)*Wp[:,None]*D
        J[...,0,1]=(U-W)[:,None]/r0*D
        J[...,1,1]=(U[:,None]*H+W[:,None]*DD)/r0
        J[...,2,2]=(U[:,None]*H+W[:,None]*TT)/r0
        B1=J@T(E)+E@T(J); B2=2*J@T(J)
        ds=2*tr(T(y)@Z)[...,None,None]; dds=2*tr(T(Z)@Z)[...,None,None]
        YY=y@T(y); YY1=Z@T(y)+y@T(Z)
        K0=a*I+b*YY
        K1=aa*ds*I+bb*ds*YY+b*YY1
        K2=(aaa*ds*ds+aa*dds)*I+(bbb*ds*ds+bb*dds)*YY+2*bb*ds*YY1+2*b*Z@T(Z)
        T1=tr(K1@B0+K0@B1); T2=tr(K2@B0+2*K1@B1+K0@B2)
        V1=(Vp*ds)[...,0,0]; V2=(Vpp*ds*ds+Vp*dds)[...,0,0]
        S=((T1+V1)*H*aw).sum(axis=1)
        rhs=np.zeros(n+1)
        for i in range(2):
            np.add.at(rhs,np.arange(n)+i,(wq*w*N*S*np.tile(shape[i],n)).reshape(n,-1).sum(axis=1))
        vv=np.zeros(n+1);vv[1:]=spsolve(K[1:,1:],rhs[1:])
        assert np.max(abs((K@vv-rhs)[1:]))<1e-8
        chi=N*(np.repeat(vv[:-1],len(t))*np.tile(shape[0],n)+np.repeat(vv[1:],len(t))*np.tile(shape[1],n))
        Cc=chi[:,None]*H
        B01=np.zeros_like(B1)
        fp=coef(r)[-2]
        B01[...,0,0]=fp[:,None]*U[:,None]*H
        B01[...,0,1]=B01[...,1,0]=(f0-1)*W[:,None]*D/r0
        C=np.linalg.solve(B0,B1-B01)-4*Cc[...,None,None]*I
        F2=T2+V2+2*Cc*T1+10*Cc*V1+20*Cc*Cc*V[...,0,0]+c[:,None]*(tr(C)**2-tr(C@C))
        return float(np.sum(wq*w*N*(F2*aw).sum(axis=1)))
    from scipy.linalg import eigh
    dim=2*degree; eye=np.eye(dim)
    Etrial=lambda v:energy(v[:degree],v[degree:])
    diagonal=np.array([Etrial(v) for v in eye])
    mat=np.diag(diagonal)
    for i in range(dim):
        for j in range(i):
            mat[i,j]=mat[j,i]=(Etrial(eye[i]+eye[j])-diagonal[i]-diagonal[j])/2
    test=np.arange(1,dim+1)*(-1.)**np.arange(dim)/dim
    assert abs(Etrial(test)-test@mat@test)<1e-8*(1+abs(test@mat@test))
    # Physical displacement L2 comparison norm, not kinetic frequency.
    gram=(P*(wq*w))@P.T
    from scipy.linalg import block_diag
    mass=block_diag(gram,L*gram)
    eig,vec=eigh(mat,mass)
    x=vec[:,0]
    assert np.linalg.norm(mat@x-eig[0]*mass@x)<1e-7*(1+np.linalg.norm(mat@x))
    assert abs(Etrial(x)-x@mat@x)<1e-7*(1+abs(x@mat@x))
    print(n,ell,degree,annulus,'min L2 Rayleigh',eig[0],'direction',x.tolist(),flush=True)
    return mat,mass

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('--n',type=int,default=64)
    parser.add_argument('--degree',type=int,default=3)
    parser.add_argument('--ell',type=int,nargs='+',default=[1,2,3,4])
    parser.add_argument('--annulus',type=float,nargs=2,default=[.15,.85])
    args=parser.parse_args()
    assert 0<args.annulus[0]<args.annulus[1]<1 and args.degree>=1
    for ell in args.ell:run(args.n,ell,args.degree,tuple(args.annulus))
