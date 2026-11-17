"""Exact SymPy Maxwell tangential transfer; no physical source calibration."""
import sympy as S
import pytest
from smith_filsinger_tangential_maxwell_sympy import (
    tangential_generator,transfer_midpoint_z,three_layer_tangential_transfer)

def test_symbolic_maxwell_tangential_projection():
    w,k,m,ex,ey,ez=S.symbols('w k m ex ey ez',nonzero=True)
    M=tangential_generator(w,k,m,ex,ey,ez)
    Ex,Ey,Hx,Hy=S.symbols('Ex Ey Hx Hy')
    d=M*S.Matrix([Ex,Ey,Hx,Hy])
    assert S.simplify(d[0]-S.I*(w*m-k*k/(w*ez))*Hy)==0
    assert S.simplify(d[1]+S.I*w*m*Hx)==0
    assert S.simplify(d[2]-S.I*(k*k/(w*m)-w*ey)*Ey)==0
    assert S.simplify(d[3]-S.I*w*ex*Ex)==0
    assert S.trace(M)==0

@pytest.mark.parametrize('kx',[S.Rational(0),S.Rational(1,2),S.Rational(2,3)])
def test_exact_reversible_transfer_at_three_wavevectors(kx):
    M=tangential_generator(2,kx,1,2,3,4)
    T=transfer_midpoint_z(M,S.Rational(1,5))
    Ti=transfer_midpoint_z(M,S.Rational(-1,5))
    assert S.simplify(T*Ti)==S.eye(4)
    assert S.simplify(T.det())==1

def test_three_layer_tangential_continuity_and_order():
    g=[tangential_generator(2,S.Rational(1,2),1,2,3,4),
       tangential_generator(2,S.Rational(1,2),1,1,1,1),
       tangential_generator(2,S.Rational(1,2),1,3,2,4)]
    d=[S.Rational(1,4),S.Rational(1,5),S.Rational(1,6)]
    T=three_layer_tangential_transfer(g,d)
    q=S.Matrix([1,2,3,4])
    q3=q
    for M,width in zip(g,d):q3=transfer_midpoint_z(M,width)*q3
    assert S.simplify(T*q-q3)==S.zeros(4,1)

def test_hall_tensor_mixes_electric_polarizations():
    w=S.Rational(2);k=S.Rational(1,2)
    g0=tangential_generator(w,k,1,1,1,1)
    gh=tangential_generator(w,k,1,1,1,1,S.Rational(1,3),S.Rational(-1,3))
    assert gh[2,0]!=0 and gh[3,1]!=0
    assert g0[2,0]==0 and g0[3,1]==0
    assert gh*S.Matrix([1,0,0,0])!=g0*S.Matrix([1,0,0,0])

def test_unphysical_longitudinal_zero_divisor_rejected():
    with pytest.raises(ValueError):
        tangential_generator(1,1,1,1,1,0)
