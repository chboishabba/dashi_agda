"""Independent exact finite checks of source-written F13 normalization."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import sys
import pytest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from zipf_f13_pnf_parity_exact import (
    source_unreduced_hurwitz_fraction, constructive_pnf_masses,
    rational_parity_certificate, pnf_constant_expectation,
)


def test_integer_grid_source_fold_and_pnf_match():
    for n,s,q in product(range(1,10),range(7),range(6)):
        cert=rational_parity_certificate(n,s,q)
        assert cert['normalized']==1


def test_zero_exponent_is_uniform():
    for n,q in product(range(1,22),range(7)):
        assert constructive_pnf_masses(n,0,q)==(F(1,n),)*n
        assert source_unreduced_hurwitz_fraction(n,0,q)==(n,1)


def test_zero_shift_independent_zipf_weights():
    for n,s in product(range(1,10),range(1,9)):
        weights=[F(1,r**s) for r in range(1,n+1)]
        z=sum(weights,F())
        assert constructive_pnf_masses(n,s,0)==tuple(w/z for w in reversed(weights))


def test_shift_and_exponent_not_interchanged():
    p=constructive_pnf_masses(3,2,1)
    raw=(F(1,16),F(1,9),F(1,4))
    assert p==tuple(x/sum(raw,F()) for x in raw)
    assert p!=constructive_pnf_masses(3,1,2)


def test_finite_hurwitz_recurrence():
    for n,s,q in product(range(1,8),range(5),range(4)):
        a,b=source_unreduced_hurwitz_fraction(n+1,s,q)
        c,d=source_unreduced_hurwitz_fraction(n,s,q)
        assert F(a,b)==F(c,d)+F(1,(n+1+q)**s)


def test_pnf_constant_expectation_signed_rates():
    for n,s,q in product(range(1,8),range(4),range(3)):
        for rate in (F(0),F(1),F(-7,3),F(100,9)):
            assert pnf_constant_expectation(n,s,q,rate)==rate


def test_iid_two_draw_collision_bridge():
    for n,s,q in product(range(1,10),range(5),range(3)):
        p=constructive_pnf_masses(n,s,q)
        collision=sum((x*x for x in p),F())
        observed_expectation=sum((1-(1-x)**2 for x in p),F())
        assert observed_expectation==2-collision


def test_rejects_invalid_domain_and_inexact_rate():
    for args in ((0,1,0),(1,-1,0),(1,0,-1),
                 (True,0,0),(2,True,0),(3,0,False)):
        with pytest.raises(ValueError):
            rational_parity_certificate(*args)
    with pytest.raises(ValueError):
        pnf_constant_expectation(2,1,0,0.25)


def test_single_type_is_one():
    for s,q in product(range(12),range(12)):
        assert constructive_pnf_masses(1,s,q)==(F(1),)
        assert pnf_constant_expectation(1,s,q,F(17,3))==F(17,3)
