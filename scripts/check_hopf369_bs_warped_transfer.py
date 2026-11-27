#!/usr/bin/env python3
"""Actual AK scalar normal transfer and longitudinal gauge pencil.
Analytic comparison bounds, plus noncertified numerical regression.
No full tensor characteristic or spectral theorem is claimed.
"""
import sympy as S
import numpy as np
from scipy.linalg import eigvals
from scipy.integrate import solve_ivp
from numpy.polynomial.legendre import leggauss

h0=4/5; j=-6/5; L=2*np.log(2); Lc=2*np.arctan(3/4)/h0

def algebra():
    h,B,k,p=S.symbols('h B k p',positive=True)
    # x is conformal normal distance, dx=dn/b. b_x=b*b_n.
    # u=b^(3/2)v, (b^4 v_n)_n=b^2 ell^2 v.
    x=S.symbols('x'); b=S.Function('b')(x); u=S.Function('u')(x); ell=S.symbols('ell')
    v=b**(-S.Rational(3,2))*u
    eq=S.expand((S.diff(b**3*S.diff(v,x),x)-b**3*ell**2*v)/b**S.Rational(3,2))
    V=S.Rational(3,2)*S.diff(b,x,2)/b+S.Rational(3,4)*(S.diff(b,x)/b)**2
    assert S.simplify(eq-(u.diff(x,2)-(ell**2+V)*u))==0
    V0=S.expand(V.subs({S.diff(b,x,2):b*(2*b*b-h*h),S.diff(b,x):b*p}).subs(p*p,b*b-h*h))
    assert S.expand(V0-(15*b*b-9*h*h)/4)==0
    # Bound from Dirichlet Green |G|<=3/|ell| exp(-alpha |x-y|).
    qmax=S.Rational(231,100); gam=S.Integer(32)
    contraction=6*qmax/gam**2
    E=18*qmax/(gam*(1-contraction))
    assert contraction< S.Rational(1,50) and E<S.Rational(4,3)
    # scalar seam conormal conversion, m,d independent and signed
    m,d,jj=S.symbols('m d j'); p0,pL=S.symbols('p0 pL')
    u0=p0+S.Rational(3,2)*(jj/2)*(m+d/2)
    uL=pL-S.Rational(3,2)*(jj/2)*(m-d/2)
    assert S.expand(u0-uL-(p0-pL+S.Rational(3,2)*jj*m))==0
    assert S.expand((u0+uL)/2-((p0+pL)/2+3*jj*d/8))==0
    # Complex gauge eigenvalue identities, inner products a,c,x,y real.
    a,c,X,Y,R,I=S.symbols('a c X Y R I',real=True)
    z=R+S.I*I; cross=a-z*X
    expr=S.expand(z*(Y-S.conjugate(cross)))
    assert S.expand(S.im(expr)-I*(Y-a))==0
    assert S.expand(S.re(expr).subs(Y,a)-(R*R+I*I)*X)==0
    assert S.expand(cross*S.conjugate(cross)-(a*a-2*a*R*X+(R*R+I*I)*X*X))==0
    print('PASS Liouville potential, exact conormal conversion, contraction and complex-pencil identities')
    print('gamma>=32: contraction <=',contraction,'endpoint error coefficient <=',E)


def warped_replay():
    # Even and odd half-interval IVPs: avoids full transfer cancellation.
    # b(x)=h0 sec(h0 (x-Lc/2)) by dx=dn/b.
    from cmath import sqrt,tanh,cosh
    for s,xi in [(32+0j,0),(32+100j,100),(32+100j,0),(32+8j,60)]:
        ell=sqrt(s*s+xi*xi); assert ell.real>=32-1e-10
        E=18*2.31/(ell.real*(1-6*2.31/(abs(ell)*ell.real)))
        def rhs(x,z):
            b=h0/np.cos(h0*x); V=(15*b*b-9*h0*h0)/4
            return [z[1],(ell*ell+V)*z[0]]
        for odd in [False,True]:
            sol=solve_ivp(rhs,[0,Lc/2],np.array([0,1] if odd else [1,0],complex),rtol=2e-11,atol=1e-12)
            assert sol.success
            a,p=sol.y[:,-1]; exact=p/a
            flat=ell/tanh(ell*Lc/2) if odd else ell*tanh(ell*Lc/2)
            err=abs(exact-flat)
            assert err<E
            print('transfer',s,xi,'odd',odd,'error',err,'bound',E)


def pencil(n):
    # Periodic continuous P1, proper normal coordinate, signed Robin terms.
    dx=L/n; M=np.zeros((n,n)); Mb=M.copy(); A=M.copy(); C=M.copy(); B=M.copy()
    nodes,weights=leggauss(5); grad=np.array([-1,1])/dx
    for i in range(n):
        ids=[i,(i+1)%n]; ix=np.ix_(ids,ids)
        for q,w in zip(nodes,weights):
            y=(i+(q+1)/2)*dx; b=h0*np.cosh(y-L/2); k=np.tanh(y-L/2)
            v=np.array([(1-q)/2,(1+q)/2]); mass=np.outer(v,v)*w*dx/2; stiff=np.outer(grad,grad)*w*dx/2
            M[ix]+=mass; Mb[ix]+=b*b*mass
            A[ix]+=b*b*stiff+8*b*b*mass; C[ix]+=b**4*stiff+4*b**4*(k*k+1)*mass; B[ix]+=2*k*b*b*mass
    A[0,0]+=2*j; C[0,0]+=-2*j
    O=np.zeros_like(A)
    vals=eigvals(np.block([[A,-B],[O,C]]),np.block([[M,O],[-B.T,Mb]]))
    vals=vals[np.argsort(vals.real)]
    assert np.all(np.isfinite(vals))
    print('P1 n=',n,'lowest 8:',vals[:8])
    print('nonreal among first 24:',sum(abs(vals[:24].imag)>1e-6))
    return vals

if __name__=='__main__':
    algebra(); warped_replay()
    for n in [32,64,128]:pencil(n)
