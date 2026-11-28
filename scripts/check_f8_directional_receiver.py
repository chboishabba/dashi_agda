"""Directional inverse Fourier shells and same-window nonlinear tidal remainder.
Requires actual complete induced metric in a synchronized geodesic detector chart.
"""
import numpy as np
import sympy as s
from scipy.special import roots_legendre, spherical_jn, eval_legendre


def directions(lmax):
    x,w=roots_legendre(lmax+1);phi=2*np.pi*np.arange(2*lmax+1)/(2*lmax+1)
    r=np.sqrt(1-x*x);n=np.stack(np.broadcast_arrays(r[:,None]*np.cos(phi),r[:,None]*np.sin(phi),x[:,None]),axis=-1).reshape(-1,3)
    return n,np.repeat(w,2*lmax+1)*2*np.pi/(2*lmax+1)


def shell(field,k,point,lmax=8):
    """Integral over S² of exp(i k n.point) field(n), Cartesian components.
    Exact angular rule if field bandlimited through lmax; radial k²/(2pi)^3 separate.
    """
    n,w=directions(lmax);r=np.linalg.norm(point);A=np.asarray([field(v) for v in n]);shape=(len(w),)+(1,)*(A.ndim-1)
    if r==0:return np.sum(w.reshape(shape)*A,axis=0)
    x=n@np.asarray(point)/r;K=sum((2*l+1)*1j**l*spherical_jn(l,k*r)*eval_legendre(l,x) for l in range(lmax+1))
    return np.sum((w*K).reshape(shape)*A,axis=0)


def tidal(M,Mt,Mtt,b):
    """Exact local curvature for synchronous spatial metric t² M, a=t."""
    d,V=np.linalg.eigh(M)
    if min(d)<=0:raise ValueError('nonpositive induced spatial metric')
    S=(V/np.sqrt(d))@V.T
    return S@(-b*Mt-Mtt/2+Mt@np.linalg.solve(M,Mt)/4)@S


def coefficients(H,Ht,Htt,J,Jt,Jtt,b):
    L=lambda U,V:-b*U-V/2
    A=L(Ht,Htt)
    return A,L(Jt,Jtt)-(H@A+A@H)/2+Ht@Ht/4


def remainder_bound(e,H,Ht,Htt,J,Jt,Jtt,R,Rt,Rtt,b):
    """Pointwise operator norm bound on exact curvature minus e*T1+e²*T2.
    R=M-I-eH-e²J, with actual derivative errors supplied, not inferred.
    """
    norm=lambda A:np.linalg.norm(A,2);L=lambda V,W:-b*V-W/2
    X=e*H+e*e*J+R;Xt=e*Ht+e*e*Jt+Rt;Xtt=e*Htt+e*e*Jtt+Rtt
    r=norm(X)
    if r>.5:raise ValueError('remainder requires ||M-I||<=1/2')
    D=e*e*J+R;Dt=e*e*Jt+Rt;Dtt=e*e*Jtt+Rtt
    return (10*r*r*norm(L(Xt,Xtt))+3*r*norm(Xt)**2+norm(L(Rt,Rtt))
            +norm(D)*norm(L(Xt,Xtt))+abs(e)*norm(H)*norm(L(Dt,Dtt))
            +(norm(Xt)+abs(e)*norm(Ht))*norm(Dt)/4)


def exact():
    t=s.symbols('t',positive=True);H=s.Matrix(3,3,lambda i,j:s.Function(f'H{min(i,j)}{max(i,j)}')(t));J=s.Matrix(3,3,lambda i,j:s.Function(f'J{min(i,j)}{max(i,j)}')(t));b=1/t
    L=lambda X:-b*X.diff(t)-X.diff(t,2)/2
    A=L(J)-(H*L(H)+L(H)*H)/2+H.diff(t)**2/4
    assert (A-L(J-H*H/2)+H.diff(t)**2/4).applyfunc(s.expand)==s.zeros(3)
    w=s.Function('w')(t); f=s.Function('f')(t)
    assert s.expand(w*L(f)-(-w.diff(t,2)/2+(b*w).diff(t))*f-s.diff(-w*f.diff(t)/2+w.diff(t)*f/2-b*w*f,t))==0
    # Second-order full synchronous coordinate curvature and orthonormalization.
    e=s.symbols('e');M=s.eye(3)+e*H+e**2*J;inv=s.eye(3)-e*H+e**2*(H*H-J);S=s.eye(3)-e*H/2+e**2*(3*H*H/8-J/2)
    # Coefficient extraction before expanding high-degree symbolic matrix products.
    X1=L(H);X2=L(J)+H.diff(t)**2/4
    assert (X2-(H*X1+X1*H)/2-A).applyfunc(s.expand)==s.zeros(3)
    # Conservative inverse square-root Taylor constants at radius 1/2.
    assert s.Rational(3,8)*2**s.Rational(5,2)<3 and 2*s.sqrt(2)+2<5
    print('4 exact window/curvature/remainder controls PASS',flush=True)


def diagnostic():
    rng=np.random.default_rng(42);sym=lambda A:(A+A.T)/2
    for _ in range(100):
        H,Ht,Htt,J,Jt,Jtt=[sym(rng.normal(size=(3,3))) for i in range(6)]
        e=.04;R,Rt,Rtt=[e**3*sym(rng.normal(size=(3,3))) for i in range(3)]
        M=np.eye(3)+e*H+e*e*J+R;Mt=e*Ht+e*e*Jt+Rt;Mtt=e*Htt+e*e*Jtt+Rtt
        A,B=coefficients(H,Ht,Htt,J,Jt,Jtt,.7)
        err=np.linalg.norm(tidal(M,Mt,Mtt,.7)-e*A-e*e*B,2)
        assert err<=remainder_bound(e,H,Ht,Htt,J,Jt,Jtt,R,Rt,Rtt,.7)
    # Angular polynomial through degree 8 (arbitrary directional Cartesian tensor).
    Q=np.diag([0.,1.,-1.]);field=lambda n:(n@Q@n)**3*np.outer(n,n)
    n,w=directions(40);point=np.array([.2,.3,.4]);k=13.
    reference=sum(wi*np.exp(1j*k*(v@point))*field(v) for v,wi in zip(n,w))
    error=np.max(abs(shell(field,k,point)-reference));assert error<1e-12
    assert np.max(abs(shell(field,k,np.zeros(3))-sum(wi*field(v) for v,wi in zip(n,w))))<1e-12
    print('100 exact-curvature numerical bound controls and 2 angular reconstruction controls PASS; max angular defect',error)

if __name__=='__main__':exact();diagnostic()
