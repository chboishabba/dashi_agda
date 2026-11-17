"""Exact source-Cayley half-step certificate, implicit midpoint and negatives."""
from dataclasses import replace
import pytest
import sympy as S
from smith_filsinger_local_causal_ade_sympy import local_spec, edge_updates, cayley_edge_step
from smith_filsinger_lorentz_ade_sympy import LorentzMaterial


def witness(a, b, h):
    p, r = h*a/2, h*b/2
    den = 1-p*r
    if den == 0:
        raise ValueError('singular inverse denominator')
    q = 1/den
    quarter = S.Rational(1, 4)
    assert p+p == h*a and r+r == h*b
    assert S.expand(p*r-quarter*h*h*a*b) == 0
    assert S.simplify((1-p*r)*q) == 1
    return p,r,q


@pytest.mark.parametrize('n', [1,2,3,4,5])
def test_actual_heterogeneous_offdiagonal_midpoint(n):
    layers = [replace(LorentzMaterial(), eps=S.Rational(i+2,3),
                      mu=S.Rational(i+3,4), alpha=S.Rational(i+4,5),
                      omega0sq=S.Rational(i+5,3)) for i in range(n)]
    spec = local_spec(n, layers=layers)
    z = S.Matrix([S.Rational(i+1,7) for i in range(4*n)])
    for edge in edge_updates(spec):
        kind,i,j,a,b=edge
        if i == j:continue
        h=S.Rational(1,9)
        p,r,q=witness(a,b,h)
        x,y=z[i],z[j]
        u=q*((1+p*r)*x+(p+p)*y)
        v=q*((r+r)*x+(1+p*r)*y)
        actual=cayley_edge_step(spec,z,edge,h)['z']
        assert S.factor(u-actual[i])==0
        assert S.factor(v-actual[j])==0
        assert S.factor(u-p*v-x-p*y)==0
        assert S.factor(v-r*u-y-r*x)==0


@pytest.mark.parametrize('a,b,h', [
    (S.Rational(3,2),S.Rational(7,5),S.Rational(1,3)),
    (S.Rational(-2),S.Rational(3,4),S.Rational(2,5)),
    (S.Rational(-4,3),S.Rational(-5,7),S.Rational(1,2))])
def test_arbitrary_rational_implicit_midpoint(a,b,h):
    p,r,q=witness(a,b,h)
    T=q*S.Matrix([[1+p*r,p+p],[r+r,1+p*r]])
    A=S.Matrix([[0,a],[b,0]])
    assert S.simplify((S.eye(2)-h*A/2)*T-(S.eye(2)+h*A/2))==S.zeros(2)
    assert T*S.zeros(2,1)==S.zeros(2,1)


def test_inconsistent_half_step_refused():
    a,b,h=S.Rational(2),S.Rational(3),S.Rational(1,5)
    p,r,q=witness(a,b,h)
    wrong=p+S.Rational(1,100)
    assert wrong+wrong != h*a
    assert wrong*r != S.Rational(1,4)*h*h*a*b


def test_singular_denominator_cannot_be_certified():
    with pytest.raises(ValueError,match='singular'):
        witness(S.Rational(4),S.Rational(1),S.Rational(1))
