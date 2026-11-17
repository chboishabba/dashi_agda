"""Exact finite two-dimensional Fourier inversion and port-work accounting."""
import sympy as S
import pytest
from smith_filsinger_periodic_fourier_green_sympy import (
    MODES,forward_periodic_2x2,inverse_periodic_2x2,
    four_mode_green_field,work_by_mode,grid_source_work)


def sources():
    return {(0,0):S.Matrix([1,0]),(0,1):S.Matrix([0,S.Rational(1,2)]),
            (1,0):S.Matrix([S.Rational(2,3),1]),
            (1,1):S.Matrix([S.Rational(-1,4),S.Rational(3,5)])}


def transfer_identity():return {k:S.eye(4) for k in MODES}


def test_all_four_modes_invert_exactly():
    src=sources(); assert inverse_periodic_2x2(forward_periodic_2x2(src))==src


def test_complete_fourier_basis_orthogonality():
    for k in MODES:
        for j in MODES:
            z=sum(((-1)**(k[0]*x[0]+k[1]*x[1]+j[0]*x[0]+j[1]*x[1])
                   for x in MODES))
            assert z==(4 if k==j else 0)


def test_four_mode_maxwell_sheet_source_response_nonzero():
    z=four_mode_green_field(transfer_identity(),sources())
    assert len(z['upper_grid'])==4
    assert any(v!=S.zeros(2,1) for v in z['upper_grid'].values())
    assert all(z['response'][k]['boundary_matrix']*z['response'][k]['lower_E']
               == S.eye(2) for k in MODES)


def test_source_work_parseval_and_outgoing_balance():
    src=sources();z=four_mode_green_field(transfer_identity(),src)
    modes,total=work_by_mode(z)
    grid=grid_source_work(src,z['upper_grid'])
    assert S.simplify(total['source']-grid)==0
    assert S.simplify(total['source']-total['exterior'])==0
    assert total['absorption']==total['residual']==0
    assert total['source']>0


def test_wrong_fourier_normalisation_double_counts_energy():
    src=sources();z=four_mode_green_field(transfer_identity(),src)
    _,total=work_by_mode(z)
    wrong=4*grid_source_work(src,z['upper_grid'])
    assert wrong!=total['source']


def test_zero_sheet_source_yields_zero_reconstructed_green_and_power():
    src={k:S.zeros(2,1) for k in MODES}
    z=four_mode_green_field(transfer_identity(),src)
    _,total=work_by_mode(z)
    assert all(v==S.zeros(2,1) for v in z['upper_grid'].values())
    assert total=={'source':0,'exterior':0,'absorption':0,'residual':0}


def test_missing_fourier_mode_is_rejected():
    with pytest.raises(ValueError):forward_periodic_2x2({(0,0):S.zeros(2,1)})
    with pytest.raises(ValueError):inverse_periodic_2x2({(0,0):S.zeros(2,1)})
