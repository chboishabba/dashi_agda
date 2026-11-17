"""Exact SymPy restricted 4x4 Maxwell outgoing-sheet Green verification."""
import sympy as S
import pytest
from smith_filsinger_radiation_green_sympy import (
    F,R,outgoing_admittance,outgoing_sheet_green,
    fixtures,flux_z,sheet_power_identity)
from smith_filsinger_tangential_maxwell_sympy import (
    three_layer_tangential_transfer,transfer_midpoint_z)

def test_zero_thickness_source_sheet_exact_two_halfspaces():
    g=outgoing_sheet_green(S.eye(4),S.Integer(2),S.Integer(0))
    assert g["upper_E"]==S.eye(2)/2
    assert g["lower_E"]==S.eye(2)/2
    assert g["boundary_matrix"]==2*S.eye(2)
    j=S.Matrix([S.Rational(3,2),S.Rational(1,3)])
    work=sheet_power_identity(g,j)
    assert work["residual"]==0 and work["absorption"]==0
    assert work["source"]==work["exterior"] and work["source"]>0

def test_outgoing_halfspace_radiation_flux_sign():
    Y=outgoing_admittance(2,0,1,1)
    e=S.Matrix([S.Rational(1),S.Rational(2)])
    assert flux_z(e,Y*e)>0 and flux_z(e,-Y*e)<0
    assert Y==R

@pytest.mark.parametrize("kx",[S.Rational(0),S.Rational(1,2)])
def test_layered_radiation_matching_and_no_loss(kx):
    gens,widths=fixtures(kx)
    T=three_layer_tangential_transfer(gens,widths)
    g=outgoing_sheet_green(T,2,kx)
    j=S.Matrix([S.Integer(1),S.Rational(1,2)])
    Et,Hi,Ho=g["upper_E"]*j,g["inside_H"]*j,g["upper_H"]*j
    assert S.simplify(R*(Hi-Ho)-j)==S.zeros(2,1)
    assert S.simplify(g["boundary_matrix"]*g["lower_E"]-S.eye(2))==S.zeros(2)
    for M,d in zip(gens,widths):
        assert S.simplify(M.conjugate().T*F+F*M)==S.zeros(4)
        U=transfer_midpoint_z(M,d)
        assert S.simplify(U.conjugate().T*F*U-F)==S.zeros(4)
    work=sheet_power_identity(g,j)
    assert work["residual"]==0 and work["absorption"]==0
    assert S.simplify(work["source"]-work["exterior"])==0
    assert work["source"]>0

def test_lossless_hall_layer_flux_and_polarization():
    gens,widths=fixtures(S.Integer(0),S.Rational(1,4))
    M=gens[-1]
    assert M.conjugate().T*F+F*M==S.zeros(4)
    T=three_layer_tangential_transfer(gens,widths)
    assert S.simplify(T.conjugate().T*F*T-F)==S.zeros(4)
    g=outgoing_sheet_green(T,2,0)
    assert g["upper_E"][0,1]!=0
    work=sheet_power_identity(g,S.Matrix([1,0]))
    assert work["residual"]==0 and work["absorption"]==0
    assert work["source"]>0

def test_evanescent_requires_separate_radiation_certificate():
    with pytest.raises(ValueError):outgoing_admittance(2,3,1,1)

def test_wrong_source_boundary_jump_sign_rejected():
    g=outgoing_sheet_green(S.eye(4),2,0)
    j=S.Matrix([1,0])
    assert R*(g["upper_H"]*j-g["inside_H"]*j)!=j
    assert R*(g["inside_H"]*j-g["upper_H"]*j)==j

def test_no_sheet_current_gives_no_green_power():
    gens,widths=fixtures(S.Rational(1,2),S.Rational(1,4))
    g=outgoing_sheet_green(three_layer_tangential_transfer(gens,widths),
                           2,S.Rational(1,2))
    j=S.zeros(2,1)
    work=sheet_power_identity(g,j)
    assert work["source"]==work["exterior"]==work["absorption"]==work["residual"]==0
    assert g["upper_E"]*j==S.zeros(2,1)

def test_lossless_source_sheet_cannot_pay_positive_load_without_source():
    g=outgoing_sheet_green(S.eye(4),2,0)
    j=S.zeros(2,1)
    work=sheet_power_identity(g,j)
    assert work["source"]==0
    hypothetical_positive_load=S.Rational(100)
    assert work["source"] != hypothetical_positive_load
