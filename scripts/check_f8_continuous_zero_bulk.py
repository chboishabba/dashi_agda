"""R^3 original-source zero-frequency quadratic bulk Fourier coefficient.
Exact angular integration; finite radial quadrature and normal discretization.
Zero frequency is a Fourier transform value, not a spatially constant R^3 field.
"""
import argparse
import numpy as np
import sympy as s
from scipy.special import roots_legendre
from check_f8_original_zero_history import radial_coefficient, bump, history
from check_f8_tt_retarded import galerkin, geometry


def angular_exact():
    x,y,z=s.symbols('x y z',real=True); n=s.Matrix([x,y,z]); I=s.eye(3)
    Q=s.diag(0,1,-1); P=I-n*n.T; E=P*Q*P-P*s.trace(P*Q)/2
    # Polynomial sphere average: odd monomials vanish; even moments use double factorials.
    def avg(f):
        out=0
        for powers,c in s.Poly(s.expand(f),x,y,z).terms():
            if any(p%2 for p in powers):continue
            out+=c*s.prod(s.factorial2(p-1) for p in powers)/s.factorial2(sum(powers)+1)
        return s.simplify(out)
    sphere=s.groebner([x*x+y*y+z*z-1],x,y,z,domain=s.QQ)
    p2=1-y*y-z*z+(y*y-z*z)**2/4
    assert sphere.reduce(s.expand(s.trace(E*E)/2-p2))[1]==0
    assert avg(p2)==s.Rational(2,5)
    B=s.diag(-2,1,1)
    assert (p2*(I/3-n*n.T)).applyfunc(avg)==s.Rational(4,105)*B
    assert s.simplify(4*s.pi*s.Rational(4,105)/(2*s.pi)**3-2/(105*s.pi**2))==0
    print('4 exact R3 angular/normalization checks PASS',flush=True)


def run(cutoff=80.,nodes=4,modes=12,final=1.2,quad=80):
    r,w=roots_legendre(nodes); k=cutoff*(r+1)/2; w=w*cutoff/2
    coeff=[radial_coefficient(ki,1.) for ki in k]
    # box=1 removes series volume normalization: now coefficients use
    # Hhat(k)=int H(x) exp(-ik.x) dx, inverse (2pi)^-3.
    sol=[galerkin(ki,lambda t,n:np.zeros_like(n),lambda t,c=c:-6*c*bump(t),1.,final,modes,quad)[1] for ki,c in zip(k,coeff)]
    def F(t,n):
        a,N=geometry(t,n); out=np.zeros_like(n)
        for ki,wi,so in zip(k,w,sol):
            h,ht,hn=history(so,t,n,modes,quad)
            out+=wi*ki**2*(-ht**2/N**2+hn**2+2*ki**2*h**2/a**2)
        return 2*out/(105*np.pi**2)
    # Bulk part alone; continuous controller triple convolution is separate.
    J,_=galerkin(0.,F,lambda t:0.,1.,final,modes,quad)
    peak=max(abs(J(t,0.)) for t in np.linspace(1.,final,121))
    assert np.isfinite(peak) and peak>0
    print('cutoff,nodes,modes,final',cutoff,nodes,modes,final,'peak Fourier J_B(0)',peak,'final',J(final,0.),flush=True)
    return peak

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--cutoff',type=float,default=80.);p.add_argument('--nodes',type=int,nargs='+',default=[4,8]);p.add_argument('--modes',type=int,default=12);p.add_argument('--final',type=float,default=1.2);a=p.parse_args()
    angular_exact()
    for n in a.nodes:run(a.cutoff,n,a.modes,a.final)
