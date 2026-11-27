"""F8 original-model endpoint welds. Algebra, not coupled PDE or apparatus acceptance."""
import sympy as s
from fractions import Fraction as Q
from math import sqrt


def inverse_current(H,P,E,q,eta,eta0,U0=0):
    """Exact reverse Maxwell current, including the initial mode and integration constant."""
    u=s.Dummy('u',real=True)
    up=E*H/2-P/(2*E)
    U=U0+s.Integral(up.subs(eta,u),(u,eta0,eta))
    J=s.diff(up,eta)+q*U-E*s.diff(H,eta)
    return U,J


def israel_second(g,K0,h,j,dnh,dnj,kappa=6):
    """Full mixed second-order extrinsic curvature and Israel stress in shell GN chart."""
    gi=g.inv(); X=gi*h; Y=gi*j; N=gi*dnh/2; M=gi*dnj/2
    K1=N-X*K0; K2=M-X*N+(X*X-Y)*K0
    I=s.eye(g.rows)
    return K1,K2,-2*(K1-s.trace(K1)*I)/kappa,-2*(K2-s.trace(K2)*I)/kappa


def normal_jet_second(g,K0,h,j,dnh,S2,kappa=6):
    """Reverse second normal coefficient for specified mixed surface stress."""
    gi=g.inv(); X=gi*h; Y=gi*j; N=gi*dnh/2
    K2=-kappa*(S2-s.trace(S2)*s.eye(g.rows)/(g.rows-1))/2
    return 2*g*(K2+X*N-(X*X-Y)*K0)


def round_trip_delay(H,eta0,x0,n,L):
    """Linear conformal round-trip delay; H(t,x) is full induced spatial tensor.
    Comoving test endpoints; unperturbed null rays. L is comoving coordinate length.
    """
    u=s.Dummy('u',real=True); x0=s.Matrix(x0); n=s.Matrix(n)
    assert s.simplify((n.T*n)[0]-1)==0
    a=H(eta0+u,x0+u*n); b=H(eta0+L+u,x0+(L-u)*n)
    return s.Integral((n.T*(a+b)*n)[0]/2,(u,0,L))


def proper_delay_phase(delay,eta0,L,ell,c,nu):
    """Arrival proper-time shift in seconds and phase lag in radians (chosen sign)."""
    dt=ell/c*s.exp(eta0+2*L)*delay
    return dt,2*s.pi*nu*dt


def bootstrap_upper(E0,C0,C1,t):
    """Comparison solution for E'<=C0 E+C1 E^(3/2), nonnegative constants.
    Raises if bound loses positivity; requires independently proved energy inequality.
    """
    import math
    if min(E0,C0,C1,t)<0: raise ValueError('nonnegative inputs required')
    if E0==0: return 0.0
    g=math.exp(C0*t/2)
    integral=2*math.expm1(C0*t/2)/C0 if C0 else t
    den=1-C1*math.sqrt(E0)*integral/2
    if den<=0: raise ValueError('bootstrap interval not certified')
    return E0*(g/den)**2


def controller():
    eta=s.symbols('eta', real=True); q=s.symbols('q', nonnegative=True)
    E=s.symbols('E', positive=True)
    H,P,U,J=[s.Function(n)(eta) for n in ('H','P','U','J')]
    up=E*H/2-P/(2*E)
    # Conformal Maxwell equation U''+qU=E H'+J; preserve the initial residual.
    residual=s.diff(up,eta)+q*U-E*s.diff(H,eta)-J
    required=(E**2*(-s.diff(H,eta,2)+q*H)-s.diff(P,eta,2)-q*P)/(2*E)
    assert s.simplify(s.diff(residual,eta).subs(s.diff(U,eta),up)-required+s.diff(J,eta))==0
    # At q=0 the undifferentiated equation fixes J itself, not just J'.
    assert s.simplify(residual.subs(q,0)-(-E*s.diff(H,eta)/2-s.diff(P,eta)/(2*E)-J))==0
    # A controller confined to a source-free region cannot cancel nonzero E4 there.
    assert s.simplify(required.subs({P:0,s.diff(P,eta,2):0})-E*(-s.diff(H,eta,2)+q*H)/2)==0
    Ua,Ja=inverse_current(H,P,E,q,eta,0)
    assert s.simplify(s.diff(Ua,eta)-up)==0
    assert s.simplify(s.diff(Ua,eta,2)+q*Ua-E*s.diff(H,eta)-Ja)==0
    return 5


def junction():
    # Gaussian normal coordinates following the ACTUAL shell; normal orientation
    # as original F8. Full induced 4x4 jets, not spatial TT truncation.
    b=s.symbols('b',positive=True); beta=s.sqrt(1+b*b); e=s.symbols('e')
    g=s.diag(-1,1/b**2,1/b**2,1/b**2); gi=g.inv()
    k=s.diag(-1/beta,-beta,-beta,-beta)
    def sym(name):
        return s.Matrix(4,4,lambda i,j:s.Symbol(f'{name}{min(i,j)}{max(i,j)}',real=True))
    h,j,n,m=map(sym,('h','j','n','m'))
    X=gi*h; Y=gi*j; N=gi*n/2; M=gi*m/2
    # g_e=g+e h+e²j; d_normal g_e=2g k+e n+e²m
    inv0=gi; inv1=-X*gi; inv2=(X*X-Y)*gi
    K1,K2,S1,S2=israel_second(g,k,h,j,n,m)
    def zero(A): return A.applyfunc(s.expand)==s.zeros(4)
    assert zero(inv0*h+inv1*g)
    assert zero(inv0*j+inv1*h+inv2*g)
    assert zero(g*K1+h*k-n/2)
    assert zero(g*K2+h*K1+j*k-m/2)
    # Israel kappa5²=6, constant tension contributes only background mixed row.
    assert zero(K2+3*S2-s.trace(S2)*s.eye(4))
    assert s.expand(s.trace(S2)-s.trace(K2))==0
    # Reverse solve all normal jets from desired mixed stress at order 2.
    recovered=normal_jet_second(g,k,h,j,n,S2)
    assert zero(recovered-m)
    # Compatibility with symmetric covariant stress: mixed tensor alone is not arbitrary.
    assert zero(g*S2+h*(-(K1-s.trace(K1)*s.eye(4))/3)+j*(-(k-s.trace(k)*s.eye(4))/3)-(g*S2+h*(-(K1-s.trace(K1)*s.eye(4))/3)+j*(-(k-s.trace(k)*s.eye(4))/3)).T)
    return 8


def detector():
    # Finite-arm linearized conformal round-trip time for comoving endpoints.
    # Hnn evaluated at (eta,x) on outgoing and incoming unperturbed null segments.
    eta,L,w,k=s.symbols('eta L w k',real=True); u=s.symbols('u',real=True)
    # Exact polynomial wave test, avoids dividing by zero at resonances.
    H=lambda t,x: 1+2*t+3*x+5*t*x
    d=s.integrate(H(eta+u,u)+H(eta+L+u,L-u),(u,0,L))/2
    assert s.expand(d-L*(1+2*eta+2*L+s.Rational(3,2)*L+s.Rational(5,2)*eta*L+s.Rational(5,2)*L**2))==0
    assert s.limit(d/L,L,0)==1+2*eta
    # Exact constant mode, and transverse differential response.
    A=s.symbols('A'); assert s.integrate(2*A,(u,0,L))/2==A*L
    assert s.integrate(2*A-(-2*A),(u,0,L))/2==2*A*L
    # Proper arrival clock t=e^eta, scale ell/c. Phase has sign by convention.
    assert s.diff(s.exp(eta+2*L),eta)==s.exp(eta+2*L)
    f=lambda t,x:s.diag(H(t,x[0]),0,0)
    assert s.expand(round_trip_delay(f,eta,[0,0,0],[1,0,0],L).doit()-d)==0
    ell,c,nu=s.symbols('ell c nu',positive=True)
    dt,phase=proper_delay_phase(d,eta,L,ell,c,nu)
    assert s.simplify(phase-2*s.pi*nu*dt)==0
    return 7


def budget():
    # Literal conditional receipt bounds, not an independent continuum proof.
    D=Q(4536110765573153915383864911903,10**300)
    R=Q(7100901973797509969638,10**300)
    U=Q(25625913306690676040506148447313974772973827225035760610806855962525604705888543158345301526058010132023028426526837691,10**300)
    low=D-R+(Q(1,25)*D-4*R)/2; high=3*U/2
    assert D-R>Q('4.536e-270')
    assert Q(1,25)*D-4*R>Q('1.814e-271')
    assert low>Q('4.6267e-270') and high<Q('3.844e-182')
    # Conditional ceiling only applies to the original normalized acceleration window.
    assert Q('1.414')**2<2 and high/(72*Q('1.414'))<Q('3.776e-184')
    # No sign can be inferred if remainder dominates the direct comparison.
    assert Q(1,25)*D-4*Q('1e-270')<0
    return 5


def stability():
    assert bootstrap_upper(1,0,0,1)==1
    assert bootstrap_upper(1,0,1,1)==4
    try: bootstrap_upper(1,0,2,1)
    except ValueError: pass
    else: raise AssertionError('must fail closed')
    return 3

if __name__=='__main__':
    counts={f.__name__:f() for f in (controller,junction,detector,budget,stability)}
    print(s.__version__, counts, 'PASS',sum(counts.values()))
