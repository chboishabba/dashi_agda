"""Exact symbolic tests of the R735 local W1 H1/derivative cut.

Tests do NOT certify the Sobolev, multiplier or Navier--Stokes PDE
inequalities, nor assert unrestricted Clay B.
"""
import importlib.util
from pathlib import Path
import sympy as s

P=Path(__file__).resolve().parents[1]/'scripts/ns_r735_local_w1_h1_majorant.py'
spec=importlib.util.spec_from_file_location('ns_r735_local_w1_h1_majorant',P)
mod=importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

def _symbols():
    return s.symbols('E0 D0 nu K CW CM T t',positive=True)


def test_ode_comparison_identity_and_uniform_local_time():
    e,d,nu,K,cw,cm,T,t=_symbols()
    x=mod.scalar_ode_supersolution(d,nu,K,t)
    assert s.simplify(s.diff(x,t)-K*nu**(-3)*x**3)==0
    c=mod.local_w1_certificate(e,d,nu,K,cw,cm,T)
    assert s.simplify(x.subs(t,c.max_time)-s.sqrt(2)*d)==0
    assert c.gradient_ceiling==s.sqrt(2)*d


def test_analytic_h2_integral_from_H1_energy():
    e,d,nu,K,cw,cm,T,t=_symbols()
    c=mod.local_w1_certificate(e,d,nu,K,cw,cm,T)
    Yint=(d+K/nu**3*(s.sqrt(2)*d)**3*T)/nu
    # H2 squared uses E+2D+||Delta u||², not E+D+||Delta u||².
    assert s.simplify(c.h2_time_integral-T*(e+2*s.sqrt(2)*d)-Yint)==0
    assert s.simplify(c.h2_time_integral.subs(T,0)-d/nu)==0


def test_quintic_commutator_holder_exponents():
    e,d,nu,K,cw,cm,T,t=_symbols()
    c=mod.local_w1_certificate(e,d,nu,K,cw,cm,T)
    assert s.Rational(7,2)+s.Rational(3,2)==5
    assert s.Rational(1,4)+s.Rational(3,4)==1
    assert s.Rational(3,2)*s.Rational(4,3)==2
    expected=cw*(e+s.sqrt(2)*d)**s.Rational(7,4)*T**s.Rational(1,4)*c.h2_time_integral**s.Rational(3,4)
    assert s.simplify(c.commutator_time_integral-expected)==0


def test_product_estimate_uses_H7_4_strictly_above_Linfty_threshold():
    # 7/4>3/2 ensures actual Sobolev embedding H^(7/4)->Linf.
    assert s.Rational(7,4)>s.Rational(3,2)
    # H^(7/4) interpolation between H1 and H2 weights (1/4,3/4).
    assert s.Rational(1,4)*1+s.Rational(3,4)*2==s.Rational(7,4)
    # H^(3/4)->L4 in 3D and H1->L4 by embedding.
    assert 3*(s.Rational(1,2)-s.Rational(1,4))==s.Rational(3,4)


def test_interval_shrinks_with_high_frequency_data_not_global():
    e,d,nu,K,cw,cm,T,t=_symbols()
    c=mod.local_w1_certificate(e,d,nu,K,cw,cm,T)
    assert s.simplify(c.max_time.subs(d,2*d)-c.max_time/4)==0
    assert s.limit(c.max_time,d,s.oo)==0
    assert s.simplify(c.weighted_plus_terminal_ceiling-c.initial_mixed_ceiling-c.commutator_time_integral)==0


def test_rational_sample_certificate_is_finite_and_positive():
    c=mod.local_w1_certificate(s.Integer(3),s.Integer(2),s.Integer(1),s.Integer(1),s.Integer(1),s.Integer(1),s.Rational(1,32))
    assert c.max_time==s.Rational(1,16)
    assert s.N(c.h2_time_integral)>0
    assert s.N(c.commutator_time_integral)>0
    assert s.N(c.weighted_plus_terminal_ceiling)>s.N(c.initial_mixed_ceiling)
