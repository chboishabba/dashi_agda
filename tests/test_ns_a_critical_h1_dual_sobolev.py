"""Test physical H1 critical Fourier bound's scaling and logic boundary.

Underlying functional inequalities are the standard dual homogeneous
Sobolev embedding and L2/L6 interpolation, not numerically proved by
these tests. No unrestricted A3 promoted.
"""
import importlib.util
from pathlib import Path
import sympy as S

P=Path(__file__).resolve().parents[1]/"scripts/ns_a_critical_h1_dual_sobolev.py"
spec=importlib.util.spec_from_file_location("ns_a_critical_h1",P)
m=importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

def test_l3_energy_interpolation_exponents():
    assert S.Rational(1,3)==S.Rational(1,2)*S.Rational(1,2)+S.Rational(1,2)*S.Rational(1,6)

def test_hhalf_stokes_bound_exactly_spatially_scale_invariant():
    E,D,lam,nu,K=S.symbols("E D lam nu K",positive=True)
    base=K**2*E*D/nu**2
    assert S.simplify(K**2*(E/lam)*(D*lam)/nu**2-base)==0

def test_energy_integrates_critical_spatial_norm_uniform_in_terminal_time():
    E0,nu,K=S.symbols("E0 nu K",positive=True)
    assert S.simplify(K**2/nu**2*E0*(E0/(2*nu))
        -K**2*E0**2/(2*nu**3))==0

def test_time_L2_Hhalf_does_not_pay_critical_serrin_continuation():
    # The inherited L4_t L3_x estimate has 2/p+3/q=3/2>1.
    assert S.Rational(2,4)+S.Rational(3,3)==S.Rational(3,2)
    assert S.Rational(2,4)+S.Rational(3,3)>1
    # A squared time-L2 Hhalf bound transforms as lambda^-2.
    assert S.Rational(-2)!=0
    assert "A3 continuation" in m.certificate()["not_claimed"]
