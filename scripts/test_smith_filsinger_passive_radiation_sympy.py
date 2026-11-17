"""Exact absorbing/F13 radiation branch, passivity and source-work tests."""
import sympy as S
import pytest
from smith_filsinger_passive_radiation_sympy import (
    outgoing_passive_wavenumber, passive_halfspace_admittance,
    passive_sheet_green, cayley_passivity_identity, exact_slab_absorption)
from smith_filsinger_oblique_maxwell_sympy import oblique_generator
from smith_filsinger_tangential_maxwell_sympy import transfer_midpoint_z
from smith_filsinger_radiation_green_sympy import F,R,sheet_power_identity,flux_z


def test_complex_absorbing_outgoing_q_exact_branch():
    eps=S.Rational(15,16)+S.I/2
    assert S.simplify(outgoing_passive_wavenumber(2,0,0,1,eps)-(2+S.I/2))==0
    y=passive_halfspace_admittance(2,0,0,1,eps)
    E=S.Matrix([1,2])
    assert S.simplify(S.re(flux_z(E,y*E)))>0


def test_evanescent_continuation_is_reactive():
    y=passive_halfspace_admittance(2,3,0,1,1)
    E=S.Matrix([1,2])
    assert S.simplify(S.re(flux_z(E,y*E)))==0
    assert S.simplify(S.im(flux_z(E,y*E)))!=0


def test_cayley_flux_operator_exact_matrix_identity():
    eps=(S.Rational(1)+S.I/2)*S.eye(3)
    m=oblique_generator(2,0,0,1,eps)
    lhs,rhs=cayley_passivity_identity(m,S.Rational(1,5))
    assert lhs==rhs
    assert S.simplify(m.conjugate().T*F+F*m)==S.diag(-1,-1,0,0)
    for state in (S.Matrix([1,0,0,0]),S.Matrix([1,1,1,0])):
        dissipated=exact_slab_absorption(m,S.Rational(1,5),state)
        assert dissipated>=0


def test_lossless_gyrotropic_cayley_flux_is_conserved():
    from smith_filsinger_oblique_maxwell_sympy import tilted_hall_permittivity
    eps=tilted_hall_permittivity(2,S.Rational(1,7),(S.Rational(3,5),S.Rational(4,5),0))
    m=oblique_generator(2,S.Rational(1,3),S.Rational(1,4),1,eps)
    lhs,rhs=cayley_passivity_identity(m,S.Rational(1,6))
    assert lhs==rhs==S.zeros(4)


def test_absorbing_single_layer_sheet_power_positive_heat():
    eps=(S.Rational(1)+S.I/2)*S.eye(3)
    m=oblique_generator(2,0,0,1,eps)
    t=transfer_midpoint_z(m,S.Rational(1,5))
    response=passive_sheet_green(t,2,0,0,1,1)
    j=S.Matrix([1,S.Rational(1,2)])
    result=sheet_power_identity(response,j)
    assert S.simplify(R*(response['inside_H']-response['upper_H'])*j-j)==S.zeros(2,1)
    assert result['residual']==0
    assert result['absorption']>0
    assert result['source']>result['exterior']>0


def test_absorbing_halfspace_sheet_work_is_radiative_not_replenishment():
    eps=S.Rational(15,16)+S.I/2
    response=passive_sheet_green(S.eye(4),2,0,0,eps,eps)
    work=sheet_power_identity(response,S.Matrix([1,0]))
    assert work['residual']==0
    assert work['source']==work['exterior']>0
    assert work['absorption']==0


def test_active_epsilon_wrong_sign_rejected():
    with pytest.raises(ValueError):
        outgoing_passive_wavenumber(2,0,0,1,1-S.I/3)


def test_cutoff_rejected_and_evanescent_admitted():
    with pytest.raises(ValueError):outgoing_passive_wavenumber(2,2,0,1,1)
    assert outgoing_passive_wavenumber(2,3,0,1,1)==S.I*S.sqrt(5)


def test_unknown_symbolic_branch_rejected_without_certificate():
    e=S.symbols('eps')
    with pytest.raises(ValueError):outgoing_passive_wavenumber(2,0,0,1,e)


def test_zero_sheet_source_no_positive_useful_power():
    response=passive_sheet_green(S.eye(4),2,0,0,1,1)
    work=sheet_power_identity(response,S.zeros(2,1))
    assert work['source']==work['exterior']==work['absorption']==0
