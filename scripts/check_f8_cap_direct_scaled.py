"""Scaled direct single-layer quadrature for original E4/SMS fixed window.
Numerical diagnostic only; no interval quadrature or full wall inverse.
"""
import math,json,sys,time
import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq
from numpy.polynomial.legendre import leggauss
import sympy as S

def run(n):
    start=time.monotonic();eps=.04;pulse=.065;scale=650.;F=lambda b:np.arcsinh(1/b)-np.sqrt(1+b*b);F0=F(1.);span=F(1/12)-F0;end=span-.05;r=math.sqrt(span*span-(11/12)**2)-.012;r0=r-eps
    def b(t,seed):
        x=np.zeros_like(t)+seed
        for _ in range(5):x+=(F(x)-F0-t)*x/np.sqrt(1+x*x)
        return x
    be=float(b(end,.088));norm=.1*quad(lambda u:math.exp(1-1/(1-u*u)),-1,1,epsabs=1e-14)[0]
    def margin(s,d):
        bs=b(s,1.);br=b(end-d,be);L=end-d-s;D2=L*L-(bs-br)**2;return (D2-r0*r0)/(np.sqrt(D2)+r0)
    sc=brentq(lambda s:float(margin(s,0.)),0.,.00045,xtol=1e-16);dc=brentq(lambda d:float(margin(0.,d)),0.,.00035,xtol=1e-16)
    u,w=leggauss(n);u=(u+1)/2;w=w/2;s=sc*u;bs=b(s,1.);swt=sc*w
    dmax=np.array([brentq(lambda d:float(margin(si,d)),0.,.00035,xtol=1e-16) for si in s]);d=dmax[:,None]*u;dw=dmax[:,None]*w;T=end-d;br=b(T,be);Dmax=margin(s[:,None],d);assert np.min(Dmax)>0
    # delta=Dmax(1-u^2); factor q^-1/2 integrated analytically by this change.
    delta=Dmax[:,:,None]*(1-u*u);rr=eps-delta;D=r0+Dmax;qq=Dmax[:,:,None]*u*u*(2*D[:,:,None]-Dmax[:,:,None]*u*u);jac=2*np.sqrt(Dmax[:,:,None])/np.sqrt(2*D[:,:,None]-Dmax[:,:,None]*u*u)
    eta=qq/(4*br[:,:,None]*bs[:,None,None]);assert eta.max()<1/16
    co=[1.]
    for j in range(24):co.append(co[-1]*(j-1.5)*(j+2.5)/((j+1)*(j+.5)))
    A=np.polynomial.polynomial.polyval(eta,co)
    Xs=1/(1-(2*s/pulse-1)**2);uw=1-10*d;Xw=1/(1-uw*uw);ur=rr/eps;Xr=1/(1-ur*ur)
    # All three flat exponentials factored before quadrature.
    expo=scale+3-Xs[:,None,None]-Xw[:,:,None]-Xr;exp=np.exp(expo)
    X=S.symbols('X');P=S.Integer(1);p=1;rad=[];C=[3/r**5,-3/r**4,3/r**3,-2/r**2,1/r]
    for j in range(7):
        coef=np.array([float(x) for x in reversed(S.Poly(P,X).all_coeffs())]);rad.append(eps**(5-j)*ur**p*np.polynomial.polynomial.polyval(Xr,coef));P=S.expand(P+2*(X*X-X)*(S.diff(P,X)-P) if p else 2*X*X*(S.diff(P,X)-P));p=1-p
    D0=sum(C[j]*rad[j] for j in range(5));D2=sum(C[j]*rad[j+2] for j in range(5));assert np.min(D0)>0 and np.min(D2)>0
    # -2*g times Green normalization 1/(2pi), and conjugation factors.
    pref=6/(math.pi*bs**2.5*np.sqrt(1+bs*bs));M=pref[:,None,None]*br[:,:,None]**1.5*A*jac*exp*swt[:,None,None]*dw[:,:,None]*w[None,None,:]/norm
    beta=np.sqrt(1+br*br);Ab=br*br*(1+br*br);Bminus=(4*br*br+7*br**4)/beta;Bprime=-(4*br*br+14*br**4+9*br**6)/(1+br*br)**2
    w1=-20*uw*Xw**2;w2=100*(-2*Xw**2-8*uw*uw*Xw**3+4*uw*uw*Xw**4)
    out=[]
    for name,fac,extra,sign in [('E4',.25,0,-1),('SMS',.5,2,1)]:
        p=fac*(-Ab*w2+(Bminus+extra*br*br*beta)*w1+Bprime-extra/2*(4*br*br+2*br**4/(1+br*br)))
        # extra correction to Bprime is multiplied by chi, NOT by its derivative.
        a0=sign*fac*br*br;v0=float(np.sum(M*p[:,:,None]*D0));v2=float(np.sum(M*a0[:,:,None]*D2));total=v0+v2
        out.append(dict(receiver=name,scaled_temporal=v0,scaled_spatial=v2,scaled_total=total,log10_abs_direct=math.log10(abs(total))-scale/math.log(10),sign=int(np.sign(total)),direct_unscaled=total*math.exp(-scale)))
    return dict(n=n,scale=scale,source_causal_limit=sc,receiver_causal_limit=dc,normalization=norm,minimum_exponent_sum=float(np.min(3+scale-expo)),rows=out,seconds=time.monotonic()-start,scope='numerical direct term only, scaled quadrature, no interval or wall correction')
if __name__=='__main__':print(json.dumps(run(int(sys.argv[1])),indent=2))
