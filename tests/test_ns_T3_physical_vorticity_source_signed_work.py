"""DASHI-original finite-mode check joining manuscript-defined T3 to B physical stretching.

Classical identity (original Navier--Stokes/vorticity calculus):
  J=curl(omega cross u)=(u.grad)omega-(omega.grad)u
   =nu Delta omega - partial_t omega, on unforced NS.
  P_nonlinear_enstrophy=-2 Re<omega,J>.
By Cauchy--Schwarz: |P|²<=4||omega||² ||J||²=4D*T3.
This is NOT coercivity of T3, a sign estimate, or Clay regularity.
Permana/Ibrahim/Lathief v4 owns the definition T3=||J||²
(Eq 3); it does not own the classical vorticity identity.
Existing DASHI exact six-mode nonzero physical B carrier is reused.
"""
from collections import defaultdict
import sympy as S

I=S.I
P=(1,0,0); Q=(0,1,2); K=(1,1,2)
def vec(k):return S.Matrix(k)
def neg(k):return tuple(-x for x in k)
def cdot(a,b):return S.simplify((S.conjugate(a).T*b)[0])
def datum(sign=1):
    u={P:S.Matrix((0,1,1)),Q:S.Matrix((1,0,0)),
       K:sign*I*S.Matrix((1,-1,0))}
    u.update({neg(k):S.conjugate(x) for k,x in list(u.items())})
    return u
def certificate(u):
    omega={k:I*vec(k).cross(x) for k,x in u.items()}
    current=defaultdict(lambda:S.zeros(3,1))
    for p,w in omega.items():
        for q,z in u.items():
            k=tuple(p[j]+q[j] for j in range(3))
            current[k]+=I*vec(k).cross(w.cross(z))
    sourceWork=stretchWork=enstrophy=S.Integer(0)
    for k,w in omega.items():
        sourceWork+=-2*S.re(cdot(w,current[k]))
        enstrophy+=cdot(w,w)
        stretch=S.zeros(3,1)
        for p,wp in omega.items():
            q=tuple(k[j]-p[j] for j in range(3))
            if q in u:stretch+=I*vec(q).dot(wp)*u[q]
        stretchWork+=2*S.re(cdot(w,stretch))
    T3=S.simplify(sum((cdot(j,j) for j in current.values()),S.Integer(0)))
    return tuple(map(S.simplify,(sourceWork,stretchWork,enstrophy,T3)))

def test_signed_physical_T3_work_matches_existing_B_production():
    for sign in (1,-1):
        physical,stretch,E,T3=certificate(datum(sign))
        assert physical==stretch==sign*8
        assert E==38 and T3>0
        assert S.simplify(physical*physical<=4*E*T3)==S.true

def test_T3_quartic_and_stretching_cubic_amplitude():
    old=certificate(datum())
    for a in (1,2,4):
        scaled={k:a*u for k,u in datum().items()}
        P,Swork,E,T=certificate(scaled)
        assert (P,Swork,E,T)==(
            a**3*old[0],a**3*old[1],a*a*old[2],a**4*old[3])

def test_T3_nonnegative_even_when_signed_stretching_changes_sign():
    P1,_,_,T1=certificate(datum(1))
    P2,_,_,T2=certificate(datum(-1))
    assert P1==8 and P2==-8
    assert T1==T2>0
