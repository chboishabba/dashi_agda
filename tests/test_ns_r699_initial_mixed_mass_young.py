"""R699 cutoff-uniform initial mixed-helicity mass, exact finite calibration.

Classical Young convolution and Cauchy--Schwarz/Sobolev on T^3:
  M_k = sum_(p+q=k) (H+_p u_p) x (H-_q u_q).
  ||M||_ell2 <= ||u||_ell1 ||u||_ell2
             <= C_s ||u||_Hs ||u||_ell2, s>3/2.
Requires true norm-one helical projectors; unconstrained rational
HelicalModeScalars do NOT imply those bounds.
Attribution: standard discrete Young/Sobolev analysis, helical source
Lei--Lin--Zhou; these exact finite calibrations are DASHI's.
Neither R735 W1 in general nor Clay B is thereby proved.
"""
from collections import defaultdict
import sympy as S

def sq(p): return sum(x*x for x in p)
def neg(p): return tuple(-x for x in p)
def conj(v): return v.applyfunc(S.conjugate)
def norm2(v): return S.simplify((conj(v).T*v)[0])
def project(p,u,sign):
    k=S.Matrix(p)
    assert k.dot(u)==0
    return (u+sign*S.I*k.cross(u)/S.sqrt(sq(p)))/2
def mixed_mass(u):
    cells=defaultdict(lambda:S.zeros(3,1))
    for p,v in u.items():
        for q,w in u.items():
            k=tuple(p[j]+q[j] for j in range(3))
            cells[k]+=project(p,v,1).cross(project(q,w,-1))
    return S.simplify(sum((norm2(v) for v in cells.values()),S.Integer(0)))
def state():
    u={(1,0,0):S.Matrix([0,2,3]),
       (0,1,0):S.Matrix([4,0,5]),
       (1,1,0):S.Matrix([1,-1,6])}
    u.update({neg(k):conj(v) for k,v in list(u.items())})
    return u

def test_norm_one_physical_helical_and_cutoff_uniform():
    u=state()
    for k,v in u.items():
        plus=project(k,v,1); minus=project(k,v,-1)
        assert S.simplify(plus+minus-v)==S.zeros(3,1)
        assert S.simplify(norm2(plus)+norm2(minus)-norm2(v))==0
    l1=sum((S.sqrt(norm2(v)) for v in u.values()),S.Integer(0))
    l2=sum((norm2(v) for v in u.values()),S.Integer(0))
    assert mixed_mass(u)>0
    assert S.N(mixed_mass(u))<=S.N(l1*l1*l2)
    for N in (1,2,4,8):
        trunc={k:v for k,v in u.items() if max(map(abs,k))<=N}
        assert S.N(mixed_mass(trunc))<=S.N(l1*l1*l2)

def test_finite_sobolev_cs_and_quartic_homogeneity():
    u=state(); s=2
    l1=sum((S.sqrt(norm2(v)) for v in u.values()),S.Integer(0))
    l2=sum((norm2(v) for v in u.values()),S.Integer(0))
    hs=sum(((1+sq(k))**s*norm2(v) for k,v in u.items()),S.Integer(0))
    cs=sum((S.Rational(1,(1+sq(k))**s) for k in u),S.Integer(0))
    assert S.N(l1*l1)<=S.N(cs*hs)
    assert S.N(mixed_mass(u))<=S.N(cs*hs*l2)
    for a in (1,2,7):
        scaled={k:a*v for k,v in u.items()}
        assert S.simplify(mixed_mass(scaled)-a**4*mixed_mass(u))==0

def test_exact_unforced_heat_shear_W1_endpoint():
    t,T=S.symbols("t T",real=True,positive=True)
    u={(1,0,0):S.Matrix([0,0,1]),
       (0,1,0):S.Matrix([0,0,2])}
    u.update({neg(k):conj(v) for k,v in list(u.items())})
    em0=mixed_mass(u)
    assert em0>0
    # (u dot grad)u=0, all active modes have |k|^2=1.
    emt=mixed_mass({k:S.exp(-t)*v for k,v in u.items()})
    assert S.simplify(emt-S.exp(-4*t)*em0)==0
    weighted=S.integrate(-S.diff(emt,t),(t,0,T))
    assert S.simplify(weighted+emt.subs(t,T)-em0)==0
