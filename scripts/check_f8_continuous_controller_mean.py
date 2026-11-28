"""Continuous R3 controller mean-wall convolution: exact angular kernel.
Finite radial band, interpolated first-order wall history, no tail certificate.
"""
import numpy as np
import sympy as s
from scipy.integrate import solve_ivp
from scipy.interpolate import CubicSpline
from scipy.special import roots_legendre
from check_f8_tt_retarded import galerkin
from check_f8_original_zero_history import radial_coefficient, bump


def angular(c,d,e):
    # c=p_hat.q_hat, d=q_hat.k_hat, e=k_hat.p_hat, all coplanar.
    two=(1+6*c*c+c**4)/4
    three=(1+c*c)*(1+d*d)*(1+e*e)/8+c*d*e
    return 4*(two+three)/35


def exact():
    # Invariant fourth moment of rotated STF Q: tr(Q²)=2, dimension five.
    # Test its unique invariant quartic on S=diag(-1,-1,2)/3.
    x,y,z=s.symbols('x y z',real=True)
    avg=lambda f:sum(c*s.prod(s.factorial2(p-1) for p in m)/s.factorial2(sum(m)+1) for m,c in s.Poly(s.expand(f),x,y,z).terms() if all(p%2==0 for p in m))
    assert avg((y*y-z*z)**4)==s.Rational(12,35)*s.Rational(2,3)**2
    # Orthogonal TT projector overlap and triple trace in common plane.
    n=s.Matrix([1,0,0]); p=s.Matrix([s.Rational(3,5),s.Rational(4,5),0]); q=s.Matrix([s.Rational(-5,13),s.Rational(12,13),0]); I=s.eye(3)
    basis=[s.diag(1,-1,0)/s.sqrt(2),s.diag(1,1,-2)/s.sqrt(6)]
    for i,j in ((0,1),(0,2),(1,2)):
        A=s.zeros(3);A[i,j]=A[j,i]=1/s.sqrt(2);basis.append(A)
    def P(v):
        L=I-v*v.T
        return s.Matrix(5,5,lambda i,j:s.trace(basis[i]*(L*basis[j]*L-L*s.trace(L*basis[j])/2)))
    A,B,C=map(P,(p,q,n)); c=(p.T*q)[0]; d=(q.T*n)[0]; e=(n.T*p)[0]
    assert A*A==A and A.trace()==2
    assert s.simplify(s.trace(A*B)-(1+6*c*c+c**4)/4)==0
    assert s.simplify(s.trace(A*B*C)-((1+c*c)*(1+d*d)*(1+e*e)/8+c*d*e))==0
    assert s.simplify(angular(c,d,e)-4*(s.trace(A*B)+s.trace(A*B*C))/35)==0
    # Fourier normalization: outer sphere and inner relative azimuth.
    assert s.simplify(2*s.pi/(2*s.pi)**3-1/(4*s.pi**2))==0
    assert s.simplify(-6*4*s.pi/(2*s.pi)**3+3/s.pi**2)==0
    print('7 exact angular / Fourier normalization checks PASS',flush=True)


def run(cutoff=80.,nodes=8,histories=12,modes=12,final=1.2,quad=80):
    # Solve radial first-order histories at Chebyshev-Lobatto nodes. Interpolate
    # unit radial response (not the oscillatory source coefficient) and restore c(q).
    kh=cutoff*(1-np.cos(np.linspace(0,np.pi,histories)))/2
    sol=[galerkin(k,lambda t,n:np.zeros_like(n),lambda t:-6*bump(t),1.,final,modes,quad)[1] for k in kh]
    a,w=roots_legendre(nodes); r=cutoff*(a+1)/2; rw=cutoff*w/2
    cp=np.array([radial_coefficient(p,1.) for p in r]); hmat=[]; qmat=[]
    for k in r:
        # Triangle variables: p, q=|k-p|, exact azimuth integration. Both input
        # radii restricted to cutoff; no alias or periodicity.
        lo=abs(k-r); hi=np.minimum(k+r,cutoff)
        q=lo[:,None]+(hi-lo)[:,None]*(a+1)/2
        qw=(hi-lo)[:,None]*w/2
        pp=r[:,None]; e=(k*k+pp*pp-q*q)/(2*k*pp); d=(k*k+q*q-pp*pp)/(2*k*q); c=(k*k-pp*pp-q*q)/(2*pp*q)
        cq=np.array([radial_coefficient(v,1.) for v in q.ravel()]).reshape(q.shape)
        hmat.append(rw[:,None]*qw*pp*q*cp[:,None]*cq*angular(c,d,e)/(4*np.pi**2*k))
        qmat.append(q)
    W=np.array(hmat); qs=np.array(qmat)
    # Scale the controller response to keep ODE absolute error meaningful.
    scale=1e8
    def rhs(t,y):
        hv=np.array([s0.sol(t)[:modes].real.sum() for s0 in sol]); interp=CubicSpline(kh,hv)
        B,V=y[:nodes],y[nodes:]
        drive=2*bump(t)*np.sum(W*interp(qs),axis=(1,2))
        return np.r_[V,scale*drive-3*V/t-r*r*B/t**2]
    ctrl=solve_ivp(rhs,(1.,final),np.zeros(2*nodes),rtol=2e-9,atol=1e-12,dense_output=True,method='DOP853')
    assert ctrl.success
    def g(t):return -3*bump(t)/np.pi**2*np.dot(rw*r*r*cp,ctrl.sol(t)[:nodes])/scale
    scaleJ=1e12
    J,_=galerkin(0.,lambda t,n:np.zeros_like(n),lambda t:scaleJ*g(t),1.,final,modes,quad)
    peak=max(abs(g(t)) for t in np.linspace(1.,final,401)); end=J(final,0.)/scaleJ
    assert np.isfinite(peak) and peak>0 and np.isfinite(end) and abs(end)>0
    print('cutoff,nodes,histories,modes',cutoff,nodes,histories,modes,'peak g_Q',peak,'final Fourier J_Q(0)',end,flush=True)
    return peak,end

if __name__=='__main__':
    exact()
    for n,h in ((6,8),(10,12),(14,16)):run(nodes=n,histories=h)
