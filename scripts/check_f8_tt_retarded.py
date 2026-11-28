"""Second-order TT F8 forcing and actual variable-time GN Galerkin consumer.
Manufactured tests only; caller must supply the original first-order history.
"""
import numpy as np
import sympy as s
from scipy.integrate import solve_ivp
from scipy.special import roots_legendre


def tt_project(A,k):
    """One Fourier coefficient; keep the homogeneous trace-free sector."""
    k=np.asarray(k,float); q=k@k; P=np.eye(3)-np.outer(k,k)/q if q else np.eye(3)
    A=(A+A.T)/2
    return P@A@P-P*np.trace(P@A)/(2 if q else 3)


def wall_forcing(H,Pi,A2,S,mu):
    """Pointwise real-space source before Fourier TT projection.
    Product A2*Pi is a convolution in Fourier, not a modewise product.
    """
    return 6*(mu*S*H-A2*Pi)


def bulk_forcing(h,dh,ddh,z):
    """Consume the existing full quadratic Ricci jet owner (#1530).
    Return spatial block before Fourier TT projection. The quadratic harmonic
    adjustment is a symmetrized spatial derivative plus a trace, hence TT zero.
    Jets are covariant coordinate metric perturbation, not relative H.
    """
    from check_f8_tensor_backreaction import ricci_jet
    Q,_,_=ricci_jet(h,dh,ddh,z)
    return 2*z*z*Q[1:4,1:4]


def geometry(t,n):
    th=np.arcsinh(t); q=th-n
    a=np.sinh(q); N=np.cosh(q)/np.cosh(th)
    return a,N


def galerkin(k,F,g,initial,final,modes=24,quad=160):
    """Scalar TT component on actual n in [0, asinh(t)-asinh(1/4)].
    F: covariant scalar wave forcing, g: inward unit-normal derivative at wall.
    k is COMOVING wavenumber. Natural Neumann and zero outer value. F/g must
    already contain Fourier TT projection and all source products. Return dense
    solution, basis and domain map. Not a certified continuum discretization.
    """
    x,wt=roots_legendre(quad); r=(x+1)/2; wt=wt/2
    freq=np.pi*(np.arange(modes)+.5); phi=np.cos(r[:,None]*freq)
    dp=-np.sin(r[:,None]*freq)*freq
    def domain(t):return np.arcsinh(t)-np.arcsinh(.25)
    def mat(A,L,B):return A.T@(L[:,None]*B)
    def rhs(t,y):
        L=domain(t); Lt=1/np.sqrt(1+t*t); n=L*r; a,N=geometry(t,n)
        A=a**3/N; B=N*a**3; C=N*a
        conv=-Lt/L*r[:,None]*dp
        M=mat(phi,wt*L*A,phi); D=mat(phi,wt*L*A,conv)
        G=mat(conv,wt*L*A,conv); V=mat(dp,wt*B/L,dp)+k*k*mat(phi,wt*L*C,phi)
        q=y[:modes]; P=y[modes:]; qd=np.linalg.solve(M,P-D@q)
        f=-phi.T@(wt*L*N*a**3*F(t,n))-t**3*g(t)*np.ones(modes)
        return np.r_[qd,D.T@qd+(G-V)@q+f]
    sol=solve_ivp(rhs,(initial,final),np.zeros(2*modes,dtype=complex),rtol=2e-9,atol=2e-11,method='DOP853',dense_output=True)
    if not sol.success:raise RuntimeError(sol.message)
    def field(t,n):return np.cos(np.asarray(n)[...,None]/domain(t)*freq)@sol.sol(t)[:modes]
    return field,sol


def exact():
    H=s.Matrix([[1,2,0],[2,-1,3],[0,3,0]]); Pi=s.Matrix([[2,0,1],[0,-3,4],[1,4,1]])
    A,A2,S,mu=s.symbols('A A2 S mu'); dnH=-6*A*Pi
    shear=-A*H*Pi+A2*Pi-mu*S*H
    assert s.expand(s.trace(H))==0 and s.trace(Pi)==0
    assert (H*dnH-6*shear-6*(mu*S*H-A2*Pi)).applyfunc(s.expand)==s.zeros(3)
    k=s.Matrix(s.symbols('k:3',real=True)); q=(k.T*k)[0]; P=s.eye(3)-k*k.T/q
    V=s.Matrix(s.symbols('v:3')); g=s.eye(3); trfree=lambda X:P*X*P-P*s.trace(P*X)/2
    assert trfree(k*V.T+V*k.T).applyfunc(s.cancel)==s.zeros(3)
    assert trfree(g).applyfunc(s.cancel)==s.zeros(3)
    assert (P*P-P).applyfunc(s.cancel)==s.zeros(3)
    # Independent full 15-component donor connection algebra: no discarded
    # scalar/vector contribution to spatial TT, even for a general p.
    E=s.diag(-1,1,1,1,1); p=s.Matrix(5,5,lambda i,j:s.Symbol(f'p{min(i,j)}{max(i,j)}'))
    def lift(a,X):
        L=s.zeros(5);L[a,4]=-E[a,a];L[4,a]=1
        return L*X+X*L.T
    V0=sum((E[a,a]*lift(a,lift(a,p)) for a in range(4)),s.zeros(5))+2*(p-E*s.trace(E*p))
    B0=sum((k[a-1]*lift(a,p) for a in range(1,4)),s.zeros(5))
    assert V0[1:4,1:4]==2*(p[0,0]-s.trace(p[1:4,1:4]))*s.eye(3)
    assert lift(0,p)[1:4,1:4]==s.zeros(3)
    assert trfree(B0[1:4,1:4]).applyfunc(s.cancel)==s.zeros(3)
    # Scalar principal GN divergence identity with actual geometry.
    t,n=s.symbols('t n',positive=True); a=s.sinh(s.asinh(t)-n); N=s.cosh(s.asinh(t)-n)/s.sqrt(1+t*t)
    U=s.Function('U')(t,n)
    expr=(-s.diff(a**3/N*U.diff(t),t)+s.diff(N*a**3*U.diff(n),n))/(N*a**3)
    want=-U.diff(t,2)/N**2+(N.diff(t)/N**3-3/(a*N))*U.diff(t)+U.diff(n,2)+(N.diff(n)/N+3*a.diff(n)/a)*U.diff(n)
    assert s.simplify(expr-want)==0
    # Moving interval map: chain rule at fixed n, physical canonical momentum.
    L=s.Function('L')(t); r=s.symbols('r'); f=t*t*r**3+t*r+r*r
    assert s.simplify(s.diff(f.subs(r,n/L),t)-(f.diff(t)-r*L.diff(t)/L*f.diff(r)).subs(r,n/L))==0
    for k0 in ([0,0,0],[1,2,3]):
        X=np.array(H,float);P0=tt_project(X,k0);assert np.allclose(tt_project(P0,k0),P0) and abs(np.trace(P0))<1e-12
        assert np.linalg.norm(P0@np.array(k0))<1e-12
    print('12 grouped exact/projection checks PASS')


def diagnostic():
    # Manufactured, not original source: smooth support well inside z=4.
    # The weak Neumann data are nonzero and the outer trace is zero.
    d=.35
    def profiles(n):
        q=n/d; a=np.maximum(0,1-q*q); mask=q<1
        p=(1+q)*a**5
        dp=(a**5-10*q*(1+q)*a**4)/d
        ddp=(-20*q*a**4-10*(1+q)*a**4+80*q*q*(1+q)*a**3)/d**2
        return p*mask,dp*mask,ddp*mask
    for k in (0.,3.):
        phase=1. if k==0 else 1.+.4j
        def F(t,n):
            a,N=geometry(t,n); beta=np.sqrt(1+t*t); q=np.arcsinh(t)-n
            Nt=N*(np.tanh(q)-t/beta)/beta; Nn=-a/beta; an=-np.cosh(q)
            p,dp,ddp=profiles(n); z=t-1; f=z**4; ft=4*z**3; ftt=12*z*z
            return phase*((-ftt/N**2+(Nt/N**3-3/(a*N))*ft)*p+f*(ddp+(Nn/N+3*an/a)*dp-k*k*p/a**2))
        def g(t):return phase*(t-1)**4/d
        errs=[]
        for modes in (12,24,48):
            field,sol=galerkin(k,F,g,1.,1.2,modes,quad=240)
            n=np.linspace(0,np.arcsinh(1.2)-np.arcsinh(.25),500)
            target=phase*.2**4*profiles(n)[0]; err=np.linalg.norm(field(1.2,n)-target)/np.linalg.norm(target)
            errs.append(err)
        assert errs[2]<errs[1]<errs[0] and errs[2]<.01
        print('manufactured k=',k,'relative L2 sampled errors',errs)

if __name__=='__main__':exact();diagnostic()
