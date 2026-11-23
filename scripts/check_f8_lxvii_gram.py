"""Native mass, hat Gram, support and weak-work diagnostics (not action equivalence)."""
import math
import sympy as sp
import numpy as np
from scipy.linalg import eigvalsh_tridiagonal
from scipy.special import roots_legendre
from ksw668_f8_weak_source import weak_source

def main():
    u=sp.symbols('u'); g=1-1/(1-u*u); D=[sp.Integer(1)]
    for n in range(4): D.append(sp.cancel(sp.diff(D[-1],u)+D[-1]*sp.diff(g,u)))
    src=[sp.Rational(2,5)*(D[4]+4*D[3]/u),sp.Rational(4,7)*(D[4]+D[3]/u-6*D[2]/u**2+6*D[1]/u**3)/u**2,(D[4]-6*D[3]/u+15*D[2]/u**2-15*D[1]/u**3)/(35*u**4)]
    fact=[sp.Rational(8,5)*(6*u**10+81*u**8-92*u**6-46*u**4+70*u**2-15),sp.Rational(32,7)*(6*u**8+54*u**6-109*u**4+58*u**2-7),sp.Rational(16,35)*(24*u**6-36*u**4+12*u**2+1)]
    prim=[sp.Rational(2,5)*(u*u*D[3]+2*u*D[2]-2*D[1]),sp.Rational(4,7)*(u**4*D[3]-3*u**3*D[2]+3*u**2*D[1]),(u**6*D[3]-12*u**5*D[2]+75*u**4*D[1]-315*u**3)/35]
    for q in range(3):
        assert sp.cancel(src[q]-fact[q]/(1-u*u)**8)==0
        assert sp.cancel(src[q]*u**(2+4*q)-sp.diff(prim[q],u)-prim[q]*sp.diff(g,u)-(27*u*u if q==2 else 0))==0
    print('6 exact factored profile / original primitive derivative identities PASS')
    for d in (3,7,11):
        assert sp.integrate((1-u*u)*u**(d-1),(u,0,1))*d*2**d==sp.Rational(2**(d+1),d+2)
        assert sp.integrate((1-u*u)**2*u**(d-1),(u,0,1))*d*2**d==sp.Rational(2**(d+3),(d+2)*(d+4))
    print('6 exact origin mass ratios PASS')
    x,w=roots_legendre(16); x=(x+1)/2; w=w/2
    qx,qw=roots_legendre(256); qx=(qx+1)/2; qw=qw/2
    B2=qw@(qx**2*np.exp(1-1/(1-qx*qx))); B4=qw@(qx**4*np.exp(1-1/(1-qx*qx)))
    F=lambda t:math.asinh(t)-math.sqrt(1+t*t)/t
    rx=math.sqrt((F(12)-F(1))**2-(1-1/12)**2)-.012
    for dr in (.008,.006,.004,.003,.002):
        r=np.arange(math.ceil(3.01/dr)+1)*dr; u=r/.04; h=dr/.04
        s=weak_source(.04,r,dr); s2=weak_source(.04,r,dr,512)
        np.testing.assert_allclose(s,s2,rtol=1e-8,atol=1e-6)
        last=r[np.flatnonzero(np.any(s!=0,axis=0))[-1]]
        margin=rx-math.log(12)-(last+dr/2)
        hatmargin=rx-math.log(12)-(last+dr)
        assert min(margin,hatmargin)>dr/2
        print('support',dr,last,margin,hatmargin, 'native guard',margin>dr/2,flush=True)
        for q,ell in enumerate((0,2,4)):
            d=3+2*ell; W=((u+h/2)**d-np.maximum(0.,u-h/2)**d)/d
            # Basis domain [0,r_outer_node], then restrict zero Dirichlet node.
            a=u[:-1,None]; b=u[1:,None]; z=a+h*x
            R=(z*z-a*a)/(b*b-a*a); L=1-R; wt=h*w*z**(d-1)
            ll=np.sum(wt*L*L,axis=1); rr=np.sum(wt*R*R,axis=1); lr=np.sum(wt*L*R,axis=1)
            diag=np.r_[ll,0]+np.r_[0,rr]; D=diag+np.r_[lr,0]+np.r_[0,lr]
            # Full row sum before restriction, not row sum of reduced Gram.
            # Exact polynomial quadrature (degree <= 14), numerical eigenspectrum.
            E=eigvalsh_tridiagonal(diag[:-1]/W[:-1],lr[:-1]/np.sqrt(W[:-2]*W[1:-1]),select='i',select_range=(0,0))[0]
            H=eigvalsh_tridiagonal(diag[:-1]/W[:-1],lr[:-1]/np.sqrt(W[:-2]*W[1:-1]),select='i',select_range=(len(r)-2,len(r)-2))[0]
            assert E>0 and np.all(lr>0) and np.all(D[:-1]>=diag[:-1])
            np.testing.assert_allclose(D[0]/W[0],2**(d+1)/(d+2),rtol=1e-12)
            np.testing.assert_allclose(diag[0]/W[0],2**(d+3)/((d+2)*(d+4)),rtol=1e-12)
            load=W*s[q]; m0=load.sum(); m1=load@(u*u)
            assert abs(m0-[0,0,27*B2][q])<1e-8 and abs(m1-[0,120*B2,99*B4][q])<1e-8
            print('gram',dr,ell,E,H,'D/W',min(D[:-1]/W[:-1]),max(D[:-1]/W[:-1]),'moments',m0,m1,flush=True)
if __name__=='__main__': main()
