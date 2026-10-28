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


def test_small_data_gradient_absorption_is_exact():
    e,d,nu,K,cw,cm,T,t=_symbols()
    c=mod.small_data_global_w1_certificate(e,d,nu,K,cw,cm)
    assert s.simplify(K*nu**(-3)*c.gradient_smallness_threshold**2-nu/2)==0
    # Poincare mean-zero Y >= X; hence at every X<=D0<=threshold,
    # K nu^-3 X^3 <= (nu/2) X <= (nu/2) Y.


def test_small_data_global_h2_budget_from_energy_and_enstrophy():
    e,d,nu,K,cw,cm,T,t=_symbols()
    c=mod.small_data_global_w1_certificate(e,d,nu,K,cw,cm)
    # ∫E<=E0/(2nu), 2∫X<=E0/nu, ∫Y<=2D0/nu.
    assert s.simplify(c.h2_infinite_time_integral-((s.Rational(3,2)*e+2*d)/nu))==0
    assert s.integrate(s.exp(-s.Rational(7,2)*nu*t),(t,0,s.oo))==s.Rational(2,7)/nu


def test_small_data_weighted_holder_closes_time_infinity_without_h2_sup():
    e,d,nu,K,cw,cm,T,t=_symbols()
    c=mod.small_data_global_w1_certificate(e,d,nu,K,cw,cm)
    expected=cw*(e+d)**s.Rational(7,4)*(s.Rational(2,7)/nu)**s.Rational(1,4)*c.h2_infinite_time_integral**s.Rational(3,4)
    assert s.simplify(c.commutator_infinite_time_integral-expected)==0
    assert s.simplify(c.weighted_plus_terminal_ceiling-c.initial_mixed_ceiling-expected)==0


def test_small_data_explicit_uniform_global_sample():
    c=mod.small_data_global_w1_certificate(s.Rational(1,2),s.Rational(1,4),1,1,2,3)
    assert c.gradient_smallness_threshold==1/s.sqrt(2)
    assert s.Rational(1,4) < c.gradient_smallness_threshold
    assert c.h2_infinite_time_integral==s.Rational(5,4)
    assert s.N(c.weighted_plus_terminal_ceiling)>0


def test_arbitrary_data_eventual_low_energy_entry_before_one_viscous_time():
    c=mod.eventual_all_data_tail_w1_certificate(s.Integer(1),1,1,1,1)
    assert c.averaging_start==0
    assert c.common_entry_time==1
    assert s.simplify(c.universal_tail_energy_ceiling-
                      2*c.enstrophy_threshold*s.exp(-2))==0
    assert s.simplify(s.exp(-2*c.common_entry_time)
                      <= c.universal_tail_energy_ceiling) is s.true


def test_arbitrary_high_energy_has_only_logarithmic_waiting_time():
    nu=s.Integer(2);K=s.Integer(3);E=s.Integer(1000)
    c=mod.eventual_all_data_tail_w1_certificate(E,nu,K,1,1)
    t0=s.log(E/(2*c.enstrophy_threshold))/(2*nu)
    assert s.simplify(c.averaging_start-t0)==0
    assert s.simplify(E*s.exp(-2*nu*t0)
                      -2*c.enstrophy_threshold)==0
    assert s.simplify(E*s.exp(-2*nu*c.common_entry_time)
                      -c.universal_tail_energy_ceiling)==0


def test_arbitrary_data_average_yields_small_h1_entry_for_each_cutoff():
    e,d,nu,K,cw,cm,T,t=_symbols()
    c=mod.eventual_all_data_tail_w1_certificate(e,nu,K,cw,cm)
    window=1/nu
    # Integral_X <= E(t0)/(2nu) <= d/nu.
    average_bound=(2*c.enstrophy_threshold)/(2*nu*window)
    assert s.simplify(average_bound-c.enstrophy_threshold)==0


def test_small_h1_absorbing_region_at_common_entry():
    e,d,nu,K,cw,cm,T,t=_symbols()
    c=mod.eventual_all_data_tail_w1_certificate(e,nu,K,cw,cm)
    assert s.simplify(K*nu**(-3)*c.enstrophy_threshold**2-nu/2)==0
    # At X<=d, the enstrophy inequality and Y>=X ensure
    # X'+nu/2*Y<=0; no Galerkin cutoff can leave the region.


def test_eventual_tail_bound_is_uniform_in_initial_energy_after_wait():
    e,d,nu,K,cw,cm,T,t=_symbols()
    c=mod.eventual_all_data_tail_w1_certificate(e,nu,K,cw,cm)
    reference=mod.small_data_global_w1_certificate(
        c.universal_tail_energy_ceiling,c.enstrophy_threshold,
        nu,K,cw,cm)
    assert s.simplify(c.universal_tail_W1_ceiling-
                      reference.weighted_plus_terminal_ceiling)==0
    assert s.simplify(c.universal_tail_energy_ceiling/
                      c.enstrophy_threshold-2*s.exp(-2))==0
    # The initial-data dependence is in the waiting time, NOT the
    # universal T>=Tentry W1 tail allowance. This says NOTHING about
    # the still-uncontrolled early/middle interval.
