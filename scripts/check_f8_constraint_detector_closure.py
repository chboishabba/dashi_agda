"""Original F8 Gauss/Codazzi second-order stress and detector pullback.
Conditional on smooth shell chart; not a solution of the coupled bulk IBVP.
"""
import sympy as s
from fractions import Fraction as Q


def constraints():
    b=s.symbols('b',positive=True); B=s.sqrt(1+b*b); e=s.symbols('e')
    rho=B-1; p=-rho+b*b/(3*B)
    S0=s.diag(-rho-1,p-1,p-1,p-1)
    x,y,z,u,v=s.symbols('x y z u v',real=True)
    pi=s.Matrix([[x,z,u],[z,y,v],[u,v,-x-y]])
    S1=s.diag(0,pi)
    dr,dp=s.symbols('dr dp'); S2=s.diag(-dr,dp,dp,dp)
    I=s.eye(4); K0=-3*S0+s.trace(S0)*I
    assert s.simplify(K0-s.diag(-1/B,-B,-B,-B))==s.zeros(4)
    def gauss(S): return 3*s.trace(S)**2-9*s.trace(S*S)-12
    assert s.simplify(gauss(S0)-6*b*b)==0
    S=S0+e*S1+e**2*S2
    assert s.simplify(s.diff(gauss(S),e).subs(e,0))==0
    r2=s.symbols('R2'); pi2=s.trace(pi*pi)
    r2expr=6*dr/B-18*B*dp-9*pi2
    assert s.simplify(s.diff(gauss(S),e,2).subs(e,0)/2-r2expr)==0
    pressure=(6*dr/B-9*pi2-r2)/(18*B)
    assert s.simplify(r2expr.subs(dp,pressure)-r2)==0
    # mixed K normal development; trace equation enforces R_nn=-4.
    k=s.MatrixSymbol('K',4,4); R=s.MatrixSymbol('R',4,4)
    kd=R-s.Trace(k)*k+4*s.Identity(4)
    assert s.expand(s.Trace(kd).doit()-(s.Trace(R)-s.Trace(k)**2+16))==0
    # principal constrained stress system in proper t: dr_t+b² div q, q_t+cs² grad dr.
    cs=1/(3*B**2); M=s.diag(cs,b*b,b*b,b*b)
    for i in range(3):
        A=s.zeros(4);A[0,i+1]=b*b;A[i+1,0]=cs
        assert M*A==(M*A).T
    D=lambda f:-b*b*s.diff(f,b)
    damp=s.diag(3*b*(1+cs),3*b,3*b,3*b)
    debt=M.applyfunc(D)-M*damp-damp.T*M
    assert s.simplify(debt[0,0]/cs+b*(6+2/(B**2)-2*b*b/B**2))==0
    assert all(s.simplify(debt[i,i]+8*b**3)==0 for i in range(1,4))
    assert s.simplify(6+2/B**2-2*b*b/B**2-(4+4/B**2))==0
    return 12


def detector():
    # Same original window: recover its tidal average from ideal displacement.
    t=s.symbols('t',positive=True); ell,c,L=s.symbols('ell c L',positive=True)
    H=s.Function('H')(t); d=L*t*H/2
    # dimensionless tidal curvature, proper-time displacement L0=L*t.
    tidal=-(s.diff(H,t,2)+2*s.diff(H,t)/t)/2
    assert s.simplify(-s.diff(d,t,2)/(L*t)-tidal)==0
    tau=s.symbols('tau',positive=True); w=s.Function('w')(tau); L0=L*c*tau/ell
    displacement=s.Function('d')(tau); k=w/L0
    # Exact integration by parts including boundary concomitant.
    assert s.simplify(s.diff(k*s.diff(displacement,tau)-s.diff(k,tau)*displacement,tau)-k*s.diff(displacement,tau,2)+s.diff(k,tau,2)*displacement)==0
    # Fourier response of second derivative filter, with boundary terms zero.
    omega=s.symbols('omega',real=True); phase=s.exp(-s.I*omega*tau)
    assert s.diff(phase,tau,2)==-omega**2*phase
    # Proper window Jacobian dT/dt=b*beta, t=c*tau/ell.
    B=s.sqrt(1+1/t**2); W=s.Function('W'); T=s.Function('T')(t)
    jac=B/t
    wp=c/ell*W(T)*jac
    assert s.simplify(wp*ell/c-W(T)*jac)==0
    # Original clock F(t)=asinh(t)-sqrt(1+t²)/t.
    assert s.simplify(s.diff(s.asinh(t)-s.sqrt(1+t*t)/t,t)-jac)==0
    assert s.simplify((-1/t**2)/jac+1/(t*B))==0
    # Necessary ideal dimensionless readout accuracy at the NEC-constrained ceiling.
    U=Q(25625913306690676040506148447313974772973827225035760610806855962525604705888543158345301526058010132023028426526837691,10**300)
    assert Q(3,2)*U/(72*Q('1.414'))<Q('3.776e-184')
    return 7


def reachability():
    # Analytic finite-dimensional autonomous or analytic-clock linear modes:
    # y'=A y; output C y. If first n output jets vanish, Cayley-Hamilton
    # forces all jets zero for constant A. Illustrative exact 3-state check.
    A=s.Matrix([[0,1,0],[0,0,1],[-2,-3,-4]])
    C=s.Matrix([[1,0,0]]); O=s.Matrix.vstack(C,C*A,C*A*A)
    assert O.det()==1
    assert A**3+4*A**2+3*A+2*s.eye(3)==s.zeros(3)
    assert C*A**3==-4*C*A**2-3*C*A-2*C
    # Flat compact pulse is nonanalytic at its left edge, despite smoothness.
    t=s.symbols('t',positive=True); f=s.exp(-1/t)
    for n in range(5): assert s.limit(s.diff(f,t,n),t,0,dir='+')==0
    assert f.subs(t,1)>0
    return 9

if __name__=='__main__':
    result={f.__name__:f() for f in (constraints,detector,reachability)}
    print(s.__version__,result,'PASS',sum(result.values()))
