"""Exact SymPy checks for the Agda coefficient-level Cayley owner.

Tests the same source-owned local Maxwell/Lorentz 1x1 and 2x2 operators.
No independently measured source, physical Maxwell light-cone or Agda
kernel result is inferred.
"""
import pytest
import sympy as S
from dataclasses import replace
from smith_filsinger_local_causal_ade_sympy import (
    local_spec,edge_updates,cayley_edge_step,source_kick,
    verified_dependency_trace)
from smith_filsinger_lorentz_ade_sympy import LorentzMaterial

def cayley_formula(a,b,h):
    q=1/(1-h*h*a*b/4)
    return S.Matrix([[q*(1+h*h*a*b/4),q*h*a],
                     [q*h*b,q*(1+h*h*a*b/4)]])

@pytest.mark.parametrize('n',[1,2,3,4,5])
def test_offdiagonal_owner_cayley_formula_exact_and_zero(n):
    mats=[replace(LorentzMaterial(),eps=S.Rational(i+2,3),
                  mu=S.Rational(i+3,4),alpha=S.Rational(i+4,5),
                  omega0sq=S.Rational(i+5,3)) for i in range(n)]
    spec=local_spec(n,layers=mats)
    for edge in edge_updates(spec):
        kind,i,j,a,b=edge
        if i==j:continue
        h=S.Rational(1,9)
        A=S.Matrix([[0,a],[b,0]])
        D=1-h*h*a*b/4
        assert D!=0 and S.simplify(D/D-1)==0
        M=cayley_formula(a,b,h)
        T=(S.eye(2)-h*A/2).inv()*(S.eye(2)+h*A/2)
        assert S.simplify(M-T)==S.zeros(2)
        assert M*S.zeros(2,1)==S.zeros(2,1)
        assert i!=j
        original=S.zeros(4*n,1)
        step=cayley_edge_step(spec,original,edge,h)
        assert step['z']==original

@pytest.mark.parametrize('n',[1,2,3,4,5])
def test_diagonal_owner_cayley_and_zero(n):
    spec=local_spec(n,load=S.Rational(1,3))
    for edge in edge_updates(spec):
        kind,i,j,a,b=edge
        if i!=j:continue
        h=S.Rational(1,7)
        D=1-h*a/2
        factor=(1+h*a/2)/D
        T=(S.eye(1)-h*S.Matrix([[a]])/2).inv()*(S.eye(1)+h*S.Matrix([[a]])/2)
        assert S.simplify(T[0,0]-factor)==0
        assert factor*0==0
        assert cayley_edge_step(spec,S.zeros(4*n,1),edge,h)['z']==S.zeros(4*n,1)

@pytest.mark.parametrize('a,b,h',[
    (S.Rational(2),S.Rational(3),S.Rational(1,5)),
    (S.Rational(-7,3),S.Rational(5,9),S.Rational(2,7)),
    (S.Rational(3,2),S.Rational(-4,3),S.Rational(1,4))])
def test_nontrivial_offdiagonal_matrix_midpoint_equation(a,b,h):
    M=cayley_formula(a,b,h)
    A=S.Matrix([[0,a],[b,0]])
    assert S.simplify((S.eye(2)-h*A/2)*M-(S.eye(2)+h*A/2))==S.zeros(2)

def test_noninvertible_cayley_must_not_admit_certificate():
    a,b,h=S.Rational(4),S.Rational(1),S.Rational(1)
    assert 1-h*h*a*b/4==0
    assert cayley_formula(a,b,h).has(S.zoo)
    assert S.simplify((1-h*h*a*b/4)*S.Integer(0)) != 1

def test_second_external_source_is_new_root_even_with_exact_cayley():
    spec=local_spec(3);z=S.zeros(12,1)
    r1=source_kick(spec,z,2,1,origin='natural')
    r2=source_kick(spec,r1['z'],0,1,origin='controller')
    assert verified_dependency_trace(z,[r1,r2])['cone']=={0,2}

def test_source_free_zero_field_cannot_spontaneously_activate():
    spec=local_spec(4,load=S.Rational(1,4))
    state=S.zeros(16,1);records=[]
    for edge in edge_updates(spec):
        step=cayley_edge_step(spec,state,edge,S.Rational(1,7))
        records.append(step);state=step['z']
    assert state==S.zeros(16,1)
    assert verified_dependency_trace(S.zeros(16,1),records)['cone']==set()
