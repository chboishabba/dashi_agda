#!/usr/bin/env python3
"""One renormalized massless complex Dirac CFT state on a global optical S1.

E[N,h,alpha]=2pi c B2(alpha)/ell - c/(24pi) int N'^2/(h*N) dx;
ell=int h/N dx; B2(alpha)=alpha^2-alpha+1/6 modulo 1.
Same E supplies 2D rho and p by lapse/spatial variation and persistent
U(1) Wilson-loop current by dE/dtheta. Polyakov trace anomaly is included.
A loop with specified return path is REQUIRED; this is not the full 4D
Einstein-Maxwell-spin-c-Dirac determinant or a plasma-engineering proof.
"""
import math
import numpy as np
import sympy as sp
pi=math.pi

def B2(alpha):
    t=alpha%1
    return t*t-t+1/6

def E(N,h,dx,alpha=.5,c=1):
    ell=np.sum(h/N)*dx
    Np=(np.roll(N,-1)-np.roll(N,1))/(2*dx)
    return 2*pi*c*B2(alpha)/ell-c/(24*pi)*np.sum(Np*Np/(h*N))*dx

def stress(N,h,dx,alpha=.5,c=1):
    ell=np.sum(h/N)*dx
    ph=np.log(N)
    F=(np.roll(ph,-1)-np.roll(ph,1))/(2*dx*h)
    Fp=(np.roll(F,-1)-np.roll(F,1))/(2*dx*h)
    state=2*pi*c*B2(alpha)/(ell**2*N**2)
    return state+c*Fp/(12*pi)+c*F*F/(24*pi),state-c*F*F/(24*pi)

def numerical_gradient_error(n):
    dx=2*pi/n
    x=np.arange(n)*dx
    N=1+.12*np.cos(x)+.035*np.sin(2*x)
    h=1+.08*np.sin(x)+.045*np.cos(3*x)
    rho,p=stress(N,h,dx)
    j=n//5;eps=1e-5
    np_=N.copy();nm=N.copy();np_[j]+=eps;nm[j]-=eps
    hp=h.copy();hm=h.copy();hp[j]+=eps;hm[j]-=eps
    dn=(E(np_,h,dx)-E(nm,h,dx))/(2*eps)/(h[j]*dx)
    dh=-(E(N,hp,dx)-E(N,hm,dx))/(2*eps)/(N[j]*dx)
    return abs(dn-rho[j]),abs(dh-p[j])

def main():
    c,F,Fp,N,ell,beta=sp.symbols('c F Fp N ell beta',real=True,nonzero=True)
    C=2*sp.pi*c*beta
    t=C/(2*ell*ell)
    rho=c*Fp/(12*sp.pi)+c*F**2/(24*sp.pi)+2*t/N**2
    p=-c*F**2/(24*sp.pi)+2*t/N**2
    dp=-c*F*Fp/(12*sp.pi)-4*t*F/N**2
    assert sp.simplify(dp+F*(rho+p))==0
    assert sp.simplify(p-rho-c*(-2*(Fp+F**2))/(24*sp.pi))==0
    assert sp.Rational(1,2)**2-sp.Rational(1,2)+sp.Rational(1,6)==-sp.Rational(1,12)
    errors=[numerical_gradient_error(n) for n in (96,192,384)]
    print('lapse/pressure same-functional variational errors:',errors)
    assert errors[0][0]>5*errors[-1][0] and errors[0][1]>5*errors[-1][1]
    assert max(errors[-1])<2e-7
    nn=np.ones(128); hh=np.ones(128); dx=2*pi/128; alpha=.31; eps=1e-5
    derivative=(E(nn,hh,dx,alpha+eps/(2*pi))-E(nn,hh,dx,alpha-eps/(2*pi)))/(2*eps)
    assert abs(derivative-(2*alpha-1)/(2*pi))<2e-9
    assert abs(E(nn,hh,dx,alpha+1)-E(nn,hh,dx,alpha))<1e-12
    assert B2(.5)<0 and B2(1/6)>0 and B2(5/6)>0
    print('PASS: zeta-renormalized optical-circle Dirac energy, Ward, trace anomaly, both metric variations, holonomy current')
    print('PASS: NS phase negative Casimir; +/-2pi/3 Wilson phase positive in THIS loop model')
    print('OPEN: 4D Hadamard spin-c determinant, Schwinger/Hall dynamics, actual MMP closed field-line geometry and global Einstein fixed point')
if __name__=='__main__':main()
