"""F8 W2 source-specific corrected two-level boundary estimate.

Input: original compatible wall Zn=-Q, Ztn=-Qt (or zero-mode j/3).
The source S=(1+k²)t³Q-eta (t³Qt)_t is NON-free data. Retains the
corrected-energy cross term and exact material source derivative debt.
No full physical Schur-gap or source-history boundedness is assumed.
"""
import sympy as s
from fractions import Fraction as F


def exact():
    t,k,eta,eps,delta=s.symbols('t k eta eps delta',positive=True)
    e0,e1=s.symbols('e0 e1',nonnegative=True)
    # Original GN 1/2 collar trace constants established by FTC, not
    # by an unproved variable-boundary Hilbert norm equivalence.
    c0=s.Rational(3500,3); c1=s.Rational(1250,3)
    lam=1+k*k
    H=lam*e0+eta*e1
    Lambda=s.symbols('Lambda',positive=True)
    trace_budget=c0*e0+c1*e1
    assert s.simplify((Lambda*H-trace_budget).subs(Lambda,c0/lam))==s.simplify((eta*c0/lam-c1)*e1)
    assert s.simplify((Lambda*H-trace_budget).subs(Lambda,c1/eta))==s.simplify((lam*c1/eta-c0)*e0)
    # Lambda=max(c0/lam,c1/eta) => |Zt(0)|² <= Lambda H.
    # Real/Hermitian pairing of boundary source S with Zt(0).
    x,y=s.symbols('x y',real=True)
    assert s.expand(eps*x*x+y*y/(4*eps)-x*y-(2*eps*x-y)**2/(4*eps))==0
    # With x=sqrt(H), y=sqrt(Lambda)*|S|:
    # wall work <=eps H+Lambda|S|²/(4eps).
    z,s0=s.symbols('z s0',real=True)
    assert s.expand(eps*(z*z/Lambda)+Lambda*s0*s0/(4*eps)-z*s0
             -(2*eps*z/Lambda-s0)**2*Lambda/(4*eps))==0
    # The correction C=eta*t³ Zt Qt must be subtracted from H.
    # Its size costs the exact source norm Qt² with no invented positivity.
    qt=s.symbols('qt',real=True)
    assert s.expand(delta*z*z/Lambda+
      Lambda*(eta*t**3*qt)**2/(4*delta)-eta*t**3*z*qt
      -(2*delta*z/Lambda-eta*t**3*qt)**2*Lambda/(4*delta))==0
    # Negative control: unbounded Qt makes Hcorr=H-eta*t³ Zt Qt arbitrarily negative.
    h,z0=s.symbols('h z0',positive=True)
    Qtest=s.symbols('Qtest',positive=True)
    assert s.limit(h-eta*t**3*z0*Qtest,Qtest,s.oo)==-s.oo
    Q=s.Function('Q')(t)
    S=lam*t**3*Q-eta*s.diff(t**3*s.diff(Q,t),t)
    target=lam*t**3*Q-eta*(3*t*t*s.diff(Q,t)+t**3*s.diff(Q,t,2))
    assert s.simplify(S-target)==0
    # Source weights explicitly require Q,Qt,Qtt, not only Q.
    assert S.has(s.diff(Q,t,2)) and S.has(s.diff(Q,t))
    # Exact smooth zero-mode presentation Q0=j/3, no M/(i*k).
    j=s.Function('j')(t)
    S0=s.simplify(S.subs(Q,j/3).doit())
    want=t**3*j/3-eta*s.diff(t**3*s.diff(j,t)/3,t)
    assert s.simplify(S0.subs(k,0)-want)==0
    print('PASS scalar Israel corrected-energy boundary source, trace Young, zero mode, negative controls')

if __name__=='__main__':exact()
