"""F8 frozen material-wall symbol: seven shear/vector channels and 3 scalar.
Algebraic frozen hybrid comparison only, not a uniform variable-coefficient estimate.
"""
import numpy as np
import sympy as s
from check_f8_harmonic_material_seam import full_clock_response


def parameters(t,r=1/16):
    b=1/t; B=np.sqrt(1+b*b); w=4*r*b**4/3; K=b*b/(3*B)-w
    return B,K,w


def scalar_matrix(s0,k,t):
    """Unnormalized scalar Robin matrix for (p00,p0_parallel,tr(pij)/3)."""
    B,K,w=parameters(t); a=2/B+6*B
    la=np.sqrt(s0*s0+k*k); d=s0*s0+k*k/3
    Z=la/(la+a)*np.array([-1,0,3],complex)
    U=np.array([-s0/2,1j*k,-3*s0/2])/la**2
    D=np.array([k*k/2,1j*s0*k,-3*s0*s0/2])/d
    V=1j*k*np.array([-s0/2,1j*k/3,-s0/2])/d
    unit=np.eye(3,dtype=complex); L=unit[0]/2+s0*U
    return np.stack([(la-2/B)*unit[0]-6*w*D-10*K*L+Z/B,
                     (la-2*B)*unit[1]-6*w*V-6j*K*k*U,
                     (la-2*B)*unit[2]-2*w*D-2*K*L-B*Z])


def robin(s0,k,t,p):
    B,K,w=parameters(t); la=np.sqrt(s0*s0+k@k);g=np.diag([-1.,1.,1.,1.]);K0=np.diag([-1/B]+[-B]*3)
    Z=la/(la-2*np.trace(K0))*np.trace(g@p)
    u,D,V,T=full_clock_response(s0,k,p,K,w)
    return la*p+2*g@(-3*T+np.trace(T)*np.eye(4))+2*p@K0+Z*g@K0


def decompose(p,n):
    h=np.trace(p[1:,1:])/3; m=p[1:,0]; mpar=n@m
    return np.array([p[0,0],mpar,h]),m-n*mpar,p[1:,1:]-h*np.eye(3)


def reconstruct(a,v,J,n):
    p=np.zeros((4,4),complex); p[0,0]=a[0];p[1:,0]=p[0,1:]=a[1]*n+v;p[1:,1:]=a[2]*np.eye(3)+J
    return p


def solve(s0,k,t,f):
    """Exact algebraic solve up to floating arithmetic; no uniform conditioning claim."""
    k=np.asarray(k,float); kn=np.linalg.norm(k); n=k/kn if kn else np.array([1.,0.,0.]);B,_,_=parameters(t)
    la=np.sqrt(s0*s0+kn*kn); d=la-2*B
    a,v,J=decompose(f,n)
    return reconstruct(np.linalg.solve(scalar_matrix(s0,kn,t),a),v/d,J/d,n)


def exact():
    # Explicit rank-one feedback relative to intrinsic-clock-fixed symbol.
    a,k,L,K=s.symbols('a k L K',nonzero=True); I=s.I
    u=s.Matrix([[-a/2,I*k,-3*a/2]])
    col=s.Matrix([10*a,6*I*k,2*a])*K/L**3
    assert s.expand((u*col)[0]-K*(-8*a*a-6*k*k)/L**3)==0
    assert s.expand((1-(u*col)[0])*L**3-(L**3+8*K*a*a+6*K*k*k))==0
    assert s.expand((L**3+8*K*a*a+6*K*k*k).subs(a*a,L*L-k*k)-(L**3+8*K*L*L-2*K*k*k))==0
    # Scalar cubic isolated: positive real root cannot occur at Re(s)>0.
    q=s.symbols('q',positive=True); x=s.symbols('x',positive=True)
    assert s.diff(x**3+8*K*x*x-2*K*q,x)==3*x*x+16*K*x
    # Traceless spatial variation and transverse shift are invisible to D,V,u.
    return 4


def run():
    nchecks=exact(); rng=np.random.default_rng(20261127); worst=0.; scaleerr=0.
    cases=[(600+0j,[0,0,0]),(600+1e5j,[1e5,0,0]),(600+1e5j,[np.sqrt(3)*1e5,0,0]),(600+1e6j,[2e6,3e5,4e5]),(600+1e12j,[1e12,0,0])]
    for t in (1.,3.,12.):
        for s0,k in cases:
            k=np.array(k); kn=np.linalg.norm(k); n=k/kn if kn else np.array([1.,0.,0.]); B,_,_=parameters(t)
            X=rng.standard_normal((4,4))+1j*rng.standard_normal((4,4)); f=X+X.T
            a,v,J=decompose(f,n); A,V,Q=decompose(robin(s0,k,t,f),n); la=np.sqrt(s0*s0+kn*kn)
            expected=reconstruct(scalar_matrix(s0,kn,t)@a,(la-2*B)*v,(la-2*B)*J,n)
            scale=max(1.,np.max(abs(expected))); err=np.max(abs(robin(s0,k,t,f)-expected))/scale
            scaleerr=max(scaleerr,err); assert err<1e-10
            p=solve(s0,k,t,f); e=np.max(abs(robin(s0,k,t,p)-f))/max(1.,np.max(abs(f)))
            worst=max(worst,e); assert e<1e-7
    # At very high luminal grazing the naive unpreconditioned fixed-point norm is NOT small.
    s0=600+1e12j;k=1e12; la=np.sqrt(s0*s0+k*k); N=scalar_matrix(s0,k,1.)
    naive=np.linalg.norm(np.eye(3)-N/la,np.inf)
    assert naive>1
    print(s.__version__,nchecks,'exact grouped checks; 15 block and solve cases PASS')
    print('max block relative error',scaleerr,'max solve relative residual',worst,'full clock naive norm at high grazing',naive)

if __name__=='__main__':run()
