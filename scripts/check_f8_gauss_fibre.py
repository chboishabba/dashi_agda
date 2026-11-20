"""Time-fibre diagnostics for original canonical Gauss evolution.
Frozen spectra are local probes, not a global phase or error certificate.
Off-node defects use the actual collocation polynomial, not RHS-derived jets.
"""
import numpy as np
import sympy as s
from math import asinh, sqrt
from scipy.optimize import brentq
from check_f8_gauss_action import a,b,c
from check_f8_gauss_banded import BandedGauss


def exact():
    z=s.symbols('z'); I=s.eye(2); e=s.ones(2,1); r=s.sqrt(3)/6
    A=s.Matrix([[s.Rational(1,4),s.Rational(1,4)-r],[s.Rational(1,4)+r,s.Rational(1,4)]])
    B=s.Matrix([[s.Rational(1,2),s.Rational(1,2)]])
    R=s.factor(1+(z*B*(I-z*A).inv()*e)[0]); assert s.simplify(R-(1+z/2+z*z/12)/(1-z/2+z*z/12))==0
    w=s.symbols('w',real=True)
    phase=2*s.atan((w/2)/(1-w*w/12)); assert s.series(phase,w,0,7).removeO()==w-w**5/720
    print('exact Gauss phase and leading phase defect PASS',flush=True)


def phase_probe(S):
    h=S.dt; T=h*S.nt
    for i in (0,S.nt//2,S.nt-1):
        L,*_=S.operators(2*i+1)
        for k in (89,179,269,359):
            z=np.linalg.eigvals(L[k]); w=abs(z.imag); om=w[np.argmin(abs(w-S.k[k]))]
            phase=lambda h:2*np.arctan2(h*om/2,1-(h*om)**2/12)
            print('frozen',i,k+1,'radial',S.k[k],'nearest',om,'max',w.max(),'phase_proxy',(phase(h)/h-phase(h/2)/(h/2))*T,flush=True)


def geometry(S,ds):
    F=lambda t:asinh(t)-sqrt(1+t*t)/t
    t=brentq(lambda t:F(t)-F(1)-ds,.5,14); z=1/t;v=-1/sqrt(1+t*t);acc=t**3/(1+t*t)**2
    amp=-6*sqrt(1-v*v)/z*np.exp(1-1/(1-(2*ds/.065-1)**2)) if 0<ds<.065 else 0.
    M,C,K=S.fe.matrices(z,v)
    return M,C,K,z,v,acc,-z**-3*amp


def stages(S,x,i):
    mat,ops,w=S.mixed(i);u,m=x;rhs=[]
    for C,A,g in ops:
        r=np.array([S.fe.mv(C,u)+m,-S.apply_A(A,u)]);r[1,0]+=g*S.src;rhs.append(r)
    return S.unpack(S.solve_mixed(mat,S.pack(np.array(rhs)),w))


def defect(S,x,i,K,theta):
    # Degree-two canonical path; derivative interpolates the two stage derivatives.
    ell=np.array([(theta-c[1])/(c[0]-c[1]),(theta-c[0])/(c[1]-c[0])])
    integ=np.array([(theta*theta/2-c[1]*theta)/(c[0]-c[1]),(theta*theta/2-c[0]*theta)/(c[1]-c[0])])
    y=x+S.dt*np.einsum('s,sunm->unm',integ,K);dy=np.einsum('s,sunm->unm',ell,K)
    M,C,Ks,z,v,acc,g=geometry(S,(i+theta)*S.dt);u,m=y;q,md=dy;mv=S.fe.mv
    left=mv(M,q)-m-v*mv(C,u)
    right=md+v*mv(C,q,True)+(1-v*v)*mv(Ks,u)+mv(M,u)*S.k2
    right[-1]+=(z+S.fe.Y[-1])**-3*q[-1];right[0]-=g*S.src
    # Convert mixed residual to canonical vector-field units, then energy norm.
    rq=S.solve(M,left);rm=right-v*mv(C,rq,True);rm[-1]-=(z+S.fe.Y[-1])**-3*rq[-1]
    def norm(u,m):
        q=S.solve(M,m+v*mv(C,u));return np.sqrt(np.maximum(0,np.sum(q*mv(M,q)+(1-v*v)*u*mv(Ks,u)+u*mv(M,u)*S.k2,axis=0)))
    d=norm(rq,rm);den=norm(*dy)+norm(dy[0]-rq,dy[1]-rm)
    return d,den


def source_probe(S):
    x=np.zeros((2,S.fe.n,S.n)); n=min(S.nt,int(np.ceil(.065/S.dt))+2)
    mx=np.zeros(2); groups=np.zeros((2,4))
    for i in range(n):
        K=stages(S,x,i)
        for j,theta in enumerate((c[0],c[1],.25,.5,.75)):
            d,den=defect(S,x,i,K,theta);g=0 if j<2 else 1
            mx[g]=max(mx[g],np.linalg.norm(d)/max(np.linalg.norm(den),1e-300))
            for q,idx in enumerate(np.array_split(np.arange(S.n),4)):
                groups[g,q]=max(groups[g,q],np.linalg.norm(d[idx])/max(np.linalg.norm(den[idx]),1e-300))
        x+=S.dt*np.einsum('s,sunm->unm',b,K)
    assert mx[0]<1e-8
    print('actual source prefix steps',n,'dt',S.dt,'node/offnode relative energy residual',mx,'quartile maxima',groups,flush=True)

if __name__=='__main__':
    exact();S=BandedGauss(360,20,3,.005);phase_probe(S);source_probe(S);source_probe(BandedGauss(360,20,3,.0025))
