"""BR280 original BR152/P0H nonradial G4 constraint data.
Axisymmetric truncated Newton multipoles; finite diagnostic, not a certified
infinite-domain solution or a self-consistent Einstein-RMHD evolution.
"""
import argparse
import numpy as np
import sympy as s
from scipy.integrate import cumulative_simpson
from scipy.interpolate import CubicSpline
from scipy.special import eval_legendre
from numpy.polynomial.legendre import leggauss
from check_hopf369_br230_233_dynamic_cut import primitive,conserved

EPS=1/2000; KAP=1.; K0=1.; P0=.25; SIGN=1.; A0=KAP*SIGN*np.sqrt(K0)*EPS


def radial_functions():
    # Literal BR152 radial derivatives, with stable origin Taylor series.
    r=s.symbols('r',positive=True)
    fp=-2*(r-s.atan(r))/r**2; gp=-2*(s.atan(r)-r/(1+r*r))/r**2
    b=(s.diff(fp,r)-fp/r)/r**2; v=-s.diff(fp,r)-fp/r; c=-gp/r
    fs=[s.diff(v,r)+b*r,2*s.diff(b,r)*r*r,2*b*r,s.diff(c,r)*r]
    direct=[s.lambdify(r,s.factor(f),'numpy') for f in fs]
    near=[s.lambdify(r,s.series(f,r,0,14).removeO(),'numpy') for f in fs]
    def read(x):
        x=np.asarray(x,dtype=float); small=x<.1
        return np.stack([np.where(small,lo(x),hi(np.where(small,1.,x))) for hi,lo in zip(direct,near)],axis=-1)
    return read


def magnetic(X):
    x,y,z=np.moveaxis(np.asarray(X),-1,0);d=1+x*x+y*y+z*z
    return 8*np.stack([2*x*z-2*y,2*x+2*y*z,1-x*x-y*y+z*z],axis=-1)/d[...,None]**3


def york(X,radial):
    X=np.asarray(X);r=np.linalg.norm(X,axis=-1);n=np.divide(X,r[...,None],out=np.zeros_like(X,dtype=float),where=r[...,None]>0);z=np.array([0.,0.,1.]);mu=n[...,2];h=np.cross(z,n)
    A,B,C,D=np.moveaxis(radial(r),-1,0)
    outer=lambda u,v:u[..., :,None]*v[...,None,:]
    return -A0*(A[...,None,None]*(outer(n,z)+outer(z,n))+B[...,None,None]*mu[...,None,None]*outer(n,n)+C[...,None,None]*mu[...,None,None]*np.eye(3)+D[...,None,None]*(outer(n,h)+outer(h,n)))


def solve(radial,R=32.,nr=1001,lmax=6):
    r=np.sinh(np.linspace(0,np.arcsinh(R),nr)); mu,w=leggauss(32);ls=np.arange(0,lmax+1,2)
    P=np.array([eval_legendre(l,mu) for l in ls]); proj=(2*ls[:,None]+1)*P*w/2
    A,B,C,D=np.moveaxis(radial(r),-1,0); U=2*(A*A+D*D); V=2*A*A+B*B+3*C*C+4*A*B+4*A*C+2*B*C-2*D*D
    Y2=A0*A0*(U[:,None]+V[:,None]*mu**2); B2=64/(1+r*r)**4
    assert np.min(Y2)>-1e-14
    def newton(f):
        modes=f@proj.T; modes[0,1:]=0; u=np.zeros_like(modes)
        for i,l in enumerate(ls):
            inner=cumulative_simpson(r**(l+2)*modes[:,i],x=r,initial=0)
            outer=np.zeros(nr);outer[1:]=r[1:]**(1-l)*modes[1:,i]
            total=cumulative_simpson(outer,x=r,initial=0); outerint=total[-1]-total
            u[1:,i]=(inner[1:]/r[1:]**(l+1)+r[1:]**l*outerint[1:])/(2*l+1)
            if l==0:u[0,i]=outerint[0]
        return u
    psi=np.ones_like(Y2); u=np.zeros((nr,len(ls)))
    for k in range(20):
        f=KAP/4*EPS**2*B2[:,None]/psi**3+Y2/(8*psi**7)
        un=newton(f);pn=1+un@P
        err=np.max(abs(un-u));psi,u=pn,un
        if err<2e-15:break
    assert err<2e-15 and np.min(psi)>=1-1e-12
    Q=KAP/4*EPS**2*(32+2*np.pi)+A0*A0/8*(32+4*np.pi/3)
    assert np.max(psi)<1+Q and 7*Q<1
    # Truncated-domain Newton solves the exterior Robin condition for every mode.
    spl=[CubicSpline(r,u[:,i],bc_type=((1,0.),(1,-(l+1)*u[-1,i]/R))) for i,l in enumerate(ls)]
    def evaluate(rr,mm):
        rr=np.asarray(rr);mm=np.asarray(mm);L=np.array([eval_legendre(l,mm) for l in ls]);p=1+sum(f(rr)*v for f,v in zip(spl,L));lap=sum((f(rr,2)+2*f(rr,1)/rr-l*(l+1)*f(rr)/rr**2)*v for f,l,v in zip(spl,ls,L));return p,lap
    return evaluate,float(psi[0,0]),k+1,err,Q


def run(R,nr,lmax):
    radial=radial_functions();read,p,it,err,Q=solve(radial,R,nr,lmax)
    r,mu=np.meshgrid([.25,.5,1.,2.,4.,8.],[-.8,0.,.6],indexing='ij');r=r.ravel();mu=mu.ravel();X=np.stack([r*np.sqrt(1-mu*mu),np.zeros_like(r),r*mu],axis=-1)
    psi,lap=read(r,mu);Y=york(X,radial);B=magnetic(X);Y2=np.sum(Y*Y,axis=(-2,-1));B2=np.sum(B*B,axis=-1)
    f=KAP/4*EPS**2*B2/psi**3+Y2/(8*psi**7); elliptic=np.max(abs(lap+f));
    div=np.zeros_like(B); step=2e-5
    for j in range(3):
        d=step*np.eye(3)[j];div+=(york(X+d,radial)[..., :,j]-york(X-d,radial)[..., :,j])/(2*step)
    mom=np.max(abs(div-A0*B));trace=np.max(abs(np.trace(Y,axis1=-2,axis2=-1)))
    # Actual P0H data in the orthonormal frame, not arbitrary RMHD fixtures.
    b=EPS*B/psi[:,None]**4;j=SIGN*np.sqrt(K0)*EPS*B/psi[:,None]**8;rho=K0-P0+np.sum(b*b,axis=-1);C=K0-2*P0
    ktrace=np.sqrt(3*KAP*(K0-P0));K=Y/psi[:,None,None]**6+ktrace*np.eye(3)/3
    ham=-8*psi**-5*lap+ktrace**2-np.sum(K*K,axis=(-2,-1))-2*KAP*rho
    minimum=1.;recover=0.
    for bb,jj,rr in zip(b,j,rho):
        U=np.r_[rr,jj,bb[1:]];q,v,bb2,pp=primitive(U,bb[0],C);recover=max(recover,np.max(abs(conserved(q,v,bb2,C)-U)));minimum=min(minimum,pp,pp+C,1-v@v)
    assert elliptic<2e-8 and mom<1e-8 and trace<1e-10 and np.max(abs(ham))<2e-7 and recover<1e-9 and minimum>0
    print('BR280',R,nr,lmax,'iterations',it,'fixed-point update',err,'central psi',p,'Q',Q,'elliptic',elliptic,'Hamiltonian',np.max(abs(ham)),'York divergence',mom,'trace',trace,'primitive recovery',recover,'margin',minimum,flush=True)
    print('BR280 common readout delta psi',list(psi-1),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--R',type=float,default=32);p.add_argument('--nr',type=int,default=1001);p.add_argument('--lmax',type=int,default=6);a=p.parse_args();run(a.R,a.nr,a.lmax)
