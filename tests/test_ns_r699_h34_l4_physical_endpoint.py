"""Exact physical finite-Fourier L4/H^(3/4) mixed-mass diagnostic.

Mathematical theorem (classical): for normalized helical H± and sharp
rectangular periodic Fourier cutoffs P_N, both uniform L4 multiplier
bounds and H^(3/4)(T³)->L4(T³) yield
  sup_N sum_k |sum_(p+q=k) H+P_Nu_p x H-P_Nu_q|²
     <= C ||u||_(H^(3/4))^4.
This needs M. Riesz's uniform Lp rectangular partial-sum theorem,
Calderon--Zygmund periodic helical multiplier bounds, and Sobolev.
This file verifies the exact physical finite convolution/Holder
identity on real divergence-free data, NOT those general theorems
or any Clay A/B continuation.
"""
from collections import defaultdict
import sympy as S

def neg(k): return tuple(-i for i in k)
def vdot(u,v): return S.simplify((S.conjugate(u).T*v)[0])
def helical(k,v,sign):
    return (v+sign*S.I*S.Matrix(k).cross(v)/
            S.sqrt(sum(a*a for a in k)))/2
def cross_convolution(f,g):
    out=defaultdict(lambda:S.zeros(3,1))
    for p,v in f.items():
        for q,w in g.items():
            out[tuple(p[i]+q[i] for i in range(3))]+=v.cross(w)
    return dict(out)
def l2_squared(f):
    return S.simplify(sum((vdot(v,v) for v in f.values()),S.Integer(0)))
def l4_fourth(f):
    # Parseval applied to the Fourier expansion of |f(x)|²
    c=defaultdict(lambda:S.Integer(0))
    for p,v in f.items():
        for q,w in f.items():
            c[tuple(p[i]-q[i] for i in range(3))]+=vdot(w,v)
    return S.simplify(sum((S.conjugate(v)*v for v in c.values()),S.Integer(0)))

def test_exact_physical_mixed_product_L4_holder():
    for n in (2,3,4):
        a=1/S.sqrt(2*n)
        u={(j,0,0):a*S.Matrix((0,0,1)) for j in range(1,n+1)}
        u.update({neg(k):S.conjugate(v) for k,v in list(u.items())})
        plus={k:helical(k,v,1) for k,v in u.items()}
        minus={k:helical(k,v,-1) for k,v in u.items()}
        M=cross_convolution(plus,minus)
        mass=l2_squared(M)
        fourth_plus=l4_fourth(plus)
        fourth_minus=l4_fourth(minus)
        assert S.simplify(fourth_plus-fourth_minus)==0
        assert S.simplify(fourth_plus*fourth_minus-mass**2).is_nonnegative
        assert S.simplify(mass-
            (S.Rational(n,12)+S.Rational(1,24*n)))==0
        assert l2_squared(u)==1

def test_three_quarters_is_the_actual_3D_L4_sobolev_exponent():
    assert 3*(S.Rational(1,2)-S.Rational(1,4))==S.Rational(3,4)
    # This exact check does NOT prove the general uniform L4
    # Fourier-projection and helical-multiplier operator bounds.
