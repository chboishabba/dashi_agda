"""Exact arbitrary kx,ky and tilted Hall Maxwell source-sheet controls."""
import sympy as S
import pytest
from smith_filsinger_oblique_maxwell_sympy import (
    oblique_generator,tilted_hall_permittivity,
    outgoing_admittance_2d,oblique_sheet_green)
from smith_filsinger_tangential_maxwell_sympy import (
    tangential_generator,three_layer_tangential_transfer)
from smith_filsinger_radiation_green_sympy import F,R,flux_z,sheet_power_identity

def test_oblique_generator_restricts_to_old_ky_zero():
    w,k,mu,ex,ey,ez=S.symbols("w k mu ex ey ez",nonzero=True)
    assert S.simplify(oblique_generator(w,k,0,mu,S.diag(ex,ey,ez))
        -tangential_generator(w,k,mu,ex,ey,ez))==S.zeros(4)

def test_tilted_hall_hermitian_and_flux_conserving():
    eps=tilted_hall_permittivity(2,S.Rational(1,5),
        (S.Rational(3,5),S.Rational(4,5),0))
    assert eps.conjugate().T==eps
    M=oblique_generator(2,0,0,1,eps)
    assert S.simplify(M.conjugate().T*F+F*M)==S.zeros(4)
    assert M!=oblique_generator(2,0,0,1,2*S.eye(3))

@pytest.mark.parametrize("kx,ky",[(S.Rational(0),S.Rational(0)),
    (S.Rational(1,2),S.Rational(1,3)),
    (S.Rational(2,3),S.Rational(1,4))])
def test_two_dimensional_outgoing_admittance_flux(kx,ky):
    Y=outgoing_admittance_2d(2,kx,ky,1,1)
    e=S.Matrix([S.Rational(2),S.Rational(1,3)])
    assert S.simplify(Y[0,1]-Y[1,0])!=0
    assert flux_z(e,Y*e)>0
    assert flux_z(e,-Y*e)<0
    if ky==0:
        from smith_filsinger_radiation_green_sympy import outgoing_admittance
        assert Y==outgoing_admittance(2,kx,1,1)

def test_oblique_tilted_hall_layer_sheet_source_flux():
    kx,ky=S.Rational(1,3),S.Rational(1,4)
    eps=tilted_hall_permittivity(S.Rational(3,2),S.Rational(1,9),
        (S.Rational(3,5),S.Rational(4,5),0))
    gens=[oblique_generator(2,kx,ky,1,2*S.eye(3)),
          oblique_generator(2,kx,ky,1,S.eye(3)),
          oblique_generator(2,kx,ky,1,eps)]
    widths=[S.Rational(1,9),S.Rational(1,13),S.Rational(1,17)]
    for M in gens:
        assert S.simplify(M.conjugate().T*F+F*M)==S.zeros(4)
    T=three_layer_tangential_transfer(gens,widths)
    assert S.simplify(T.conjugate().T*F*T-F)==S.zeros(4)
    g=oblique_sheet_green(T,2,kx,ky)
    assert g["upper_E"][0,1]!=0
    j=S.Matrix([S.Rational(1),S.Rational(1,2)])
    assert S.simplify(R*(g["inside_H"]-g["upper_H"])*j-j)==S.zeros(2,1)
    work=sheet_power_identity(g,j)
    assert work["residual"]==0 and work["absorption"]==0
    assert work["source"]>0 and work["source"]==work["exterior"]

def test_longitudinal_permittivity_singularity_rejected():
    with pytest.raises(ValueError):
        oblique_generator(2,1,1,1,S.diag(1,1,0))

def test_outgoing_2d_cutoff_and_evanescent_rejected():
    with pytest.raises(ValueError):outgoing_admittance_2d(2,2,0,1,1)
    with pytest.raises(ValueError):outgoing_admittance_2d(2,2,1,1,1)
