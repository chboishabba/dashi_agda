"""Pareto digit/inequality identities and exact non-equivalence tests."""
from fractions import Fraction as F
from math import isclose
from pathlib import Path
import sys
import pytest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import pareto_benford_lorenz_bridge as P

def test_integer_shape_pareto_base_digit_exact_telescope():
    for base in (2,3,5,10,16):
        for alpha in (1,2,4):
            p=[P.pareto_leading_digit_exact(base,d,alpha) for d in range(1,base)]
            assert sum(p,F())==1
            assert all(a>b for a,b in zip(p,p[1:]))

def test_pareto_is_not_automatically_benford():
    assert P.pareto_leading_digit_exact(10,1,1)==F(5,9)
    assert P.pareto_leading_digit_exact(10,1,2)==F(25,33)
    assert abs(float(P.pareto_leading_digit_exact(10,1,1))-P.benford_digit(10,1))>0.2

def test_small_shape_limit_recovers_benford_but_alpha_zero_is_improper():
    for base in (3,10,16):
        for digit in (1,base-1):
            for shape,tol in ((1e-4,6e-5),(1e-6,6e-7)):
                assert abs(P.pareto_leading_digit(base,digit,shape)-P.benford_digit(base,digit))<tol
    with pytest.raises(ValueError): P.pareto_leading_digit(10,1,0)

def test_exact_and_float_digit_agree_for_integer_exponent():
    for a in (1,2,3):
        for digit in range(1,10):
            assert isclose(P.pareto_leading_digit(10,digit,a),float(P.pareto_leading_digit_exact(10,digit,a)),abs_tol=1e-15)

def test_pareto_lorenz_and_top_share_are_same_curve():
    for shape in (1.1,1.5,2,5):
        for t in (.1,.2,.5,.9):
            assert isclose(P.pareto_top_share(t,shape),1-P.pareto_lorenz(1-t,shape))
        assert P.pareto_lorenz(0,shape)==0
        assert P.pareto_lorenz(1,shape)==1

def test_pareto_gini_value_and_shape_sensitivity():
    assert isclose(P.pareto_gini(2),1/3)
    assert isclose(P.pareto_gini(3),1/5)
    assert P.pareto_top_share(.2,2)<.8

def test_80_20_requires_specific_pareto_shape():
    shape=P.shape_for_top_share(.2,.8)
    assert 1<shape<1.2
    assert isclose(P.pareto_top_share(.2,shape),.8,abs_tol=1e-12)
    assert isclose(P.pareto_gini(shape),1/(2*shape-1))

def test_no_lorenz_claim_when_mean_is_infinite():
    for alpha in (0,.5,1):
        with pytest.raises(ValueError): P.pareto_lorenz(.5,alpha)
        with pytest.raises(ValueError): P.pareto_top_share(.2,alpha)
        with pytest.raises(ValueError): P.pareto_gini(alpha)

def test_pareto_digit_domain_checks():
    for args in ((10,0,1),(10,10,1),(1,1,1),(10,1,0)):
        with pytest.raises(ValueError): P.pareto_leading_digit_exact(*args)
    with pytest.raises(ValueError): P.shape_for_top_share(.8,.2)
