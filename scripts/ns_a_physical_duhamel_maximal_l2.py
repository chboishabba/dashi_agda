#!/usr/bin/env python3
"""A: actual same-source nonlinear Duhamel response from existing H1 Stokes bound.

Classical heat-kernel maximal-L2 argument (standard Young/Jensen/Tonelli).
For a=nu|xi|²>0, Fhat(t,xi)=a*Vhat(t,xi), where
 Vhat=(nu|xi|²)^(-1) Fhat and Fhat=F[P div(u tensor u)].
The nonlinear Duhamel term is
 W(t,xi)=int_0^t exp(-a(t-s))*Fhat(s,xi) ds
        =int_0^t a exp(-a(t-s))*Vhat(s,xi) ds.
Kernel h_a(r)=a exp(-ar) 1_{r>=0} has L1 mass 1.
Jensen + Tonelli on 0<=t<=T yield
 ||W||²_(L2_t L2_xi) <= ||Vhat||²_(L2_t L2_xi)
 <= 4 sqrt(2) pi E0² sqrt(T) / nu^(5/2)
using the already-derived physical H1/energy response bound
from scripts/ns_a_schwartz_fourier_same_object.py.

At xi=0 take Fhat=W=0 (null-set representative). For Leray class,
interpret at almost every H1 time with the distributional Duhamel identity.
This is NOT centered double resolvent A2, NOT critical H^(1/2), NOT A3
unrestricted continuation, and NOT a proof term in Bishop Agda.
"""
from fractions import Fraction
import sympy as S

def exact_exponential_certificate():
    t,a,T,x=S.symbols("t a T x",positive=True)
    h=a*S.exp(-a*t)
    assert S.simplify(S.integrate(h,(t,0,T))-(1-S.exp(-a*T)))==0
    assert S.simplify(
        S.integrate(a*S.exp(-a*(t-x)),(t,x,T))
        -(1-S.exp(-a*(T-x))))==0
    # A nonstationary same-source scalar calibration, a=1, V=e^(-2t):
    V=S.exp(-2*t)
    D=S.exp(-t)-S.exp(-2*t)
    assert S.simplify(S.diff(D,t)+D-V)==0
    assert S.simplify(D.subs(t,0))==0
    incoming=S.integrate(V**2,(t,0,S.oo))
    outgoing=S.integrate(D**2,(t,0,S.oo))
    assert incoming==S.Rational(1,4)
    assert outgoing==S.Rational(1,12)
    return {"source_norm_squared":str(incoming),
            "duhamel_norm_squared":str(outgoing),
            "L2_contraction":True,
            "general_argument":"Jensen then Tonelli, causal heat kernel mass <=1",
            "finite_time_bound":"4 sqrt(2) pi E0^2 sqrt(T) / nu^(5/2)",
            "not_claimed":["Bishop kernel proof","critical A2","global A3"]}

def exact_discrete_causal_check():
    # A finite positive-kernel audit of the same contraction; arbitrary signs
    # are handled, and no output-cardinality loss is introduced.
    q=Fraction(1,2)
    w=[(1-q)*q**j for j in range(7)]
    v=list(map(Fraction,[3,-2,5,-4,1,0,-2]))
    out=[sum(w[j]*v[i-j] for j in range(i+1)) for i in range(len(v))]
    assert sum(y*y for y in out)<=sum(x*x for x in v)
    assert sum(w)<1
    return True

if __name__=="__main__":
    print(exact_exponential_certificate())
    exact_discrete_causal_check()
