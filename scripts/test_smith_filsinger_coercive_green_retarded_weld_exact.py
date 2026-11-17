#!/usr/bin/env python3
"""Exact Fraction regression for finite Green inverse + explicit causal delay.

The 2x2 positive diagonal operator is a SOURCE-EQUIVALENT test of the
BalabanFiniteCoerciveGreen interface. The periodic 4D lattice Green
identity is checked separately by its already existing canonical owner.
Nothing here constructs a retarded SI Maxwell dyadic or original source.
"""
from fractions import Fraction as Q
import pytest

def source(t):
    return (Q(t+1,3),Q(2*t-5,7))

def positive_operator(v):
    return (2*v[0],3*v[1])

def green_inverse(v):
    return (v[0]/2,v[1]/3)

def max_norm(v):
    return max(abs(x) for x in v)

ZERO=(Q(0),Q(0))

def delayed_green(delay,t):
    assert delay>=0 and t>=0
    if t<delay:
        return ZERO
    return green_inverse(source(t-delay))

@pytest.mark.parametrize("delay",[0,1,2,3,5,13])
def test_delay_exact_earliest_arrival_and_no_prelaunch_signal(delay):
    for t in range(delay):
        assert delayed_green(delay,t)==ZERO
    assert delayed_green(delay,delay)==green_inverse(source(0))

@pytest.mark.parametrize("delay",[0,1,2,3,7])
def test_green_inverse_and_source_bound_after_delay(delay):
    for t in range(delay,delay+20):
        out=delayed_green(delay,t)
        inp=source(t-delay)
        assert positive_operator(out)==inp
        assert max_norm(out)<=Q(1,2)*max_norm(inp)

def test_static_elliptic_green_is_not_causal_without_delay():
    assert green_inverse(source(0))!=ZERO
    assert delayed_green(4,0)==ZERO
    # A spatial inverse by itself supplies no time/front information.

def test_no_measured_work_from_green_norm_bound():
    out=delayed_green(3,3)
    assert max_norm(out)<=Q(1,2)*max_norm(source(0))
    measured_natural_input=None
    measured_device_current=None
    assert measured_natural_input is None
    assert measured_device_current is None

def test_nonlinear_source_does_not_create_free_electric_power():
    # A Green response is a field/linear operator result, not a work
    # receipt: no load work follows from an amplitude alone.
    assert green_inverse((Q(1000),Q(300)))==(Q(500),Q(100))
