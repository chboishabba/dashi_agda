"""Negative/positive causal-front controls from the original Smith donor."""
import math
import numpy as np
import pytest
from scripts.v2_retarded_causal_network_maxcut import (
    C_M_PER_S, CausalLink, delayed_samples, route_signal,
    route_receipt, quasistatic_scale, run)


def link(d=.5,velocity=.7*C_M_PER_S,gain=1.0):
    return CausalLink('synthetic',d,velocity,gain)


def test_vacuum_light_cone():
    l=link(3,C_M_PER_S)
    assert l.delay_s==pytest.approx(3/C_M_PER_S)
    assert l.vacuum_lower_bound_s==pytest.approx(l.delay_s)


def test_slow_medium_not_exactly_c():
    l=link(3,.6*C_M_PER_S)
    assert l.delay_s > l.vacuum_lower_bound_s


@pytest.mark.parametrize('speed',[C_M_PER_S*1.000001,float('inf'),0.,-1.])
def test_superluminal_or_invalid_front_rejected(speed):
    with pytest.raises(ValueError): link(1,speed).validate()


@pytest.mark.parametrize('distance',[-1.,float('nan'),float('inf')])
def test_invalid_distance_rejected(distance):
    with pytest.raises(ValueError): link(distance).validate()


@pytest.mark.parametrize('gain',[-.1,1.1,float('inf')])
def test_passive_gain_bound(gain):
    with pytest.raises(ValueError):link(gain=gain).validate()


def test_positive_distance_no_same_sample_instantaneous_effect():
    source=np.zeros(10);source[0]=1
    response=delayed_samples(source,link(0.001,C_M_PER_S),1e-4)
    assert response[0]==0 and response[1]==1


def test_zero_distance_allows_local_response():
    src=np.array([1.,2.,-3.])
    assert np.array_equal(delayed_samples(src,link(0),1e-4),src)


def test_exact_nanoscale_impulse_arrival():
    source=np.zeros(20);source[0]=1
    l=link(C_M_PER_S*3e-9,C_M_PER_S,.8)
    response=delayed_samples(source,l,1e-9)
    assert np.count_nonzero(response)==1
    assert response[3]==pytest.approx(.8)
    assert np.all(response[:3]==0)


def test_two_hop_begins_only_after_both_delays():
    source=np.zeros(40);source[0]=1
    legs=[link(C_M_PER_S*2e-9,C_M_PER_S,.8),
          link(C_M_PER_S*4e-9,C_M_PER_S,.5)]
    rec=route_receipt(legs,1e-9)
    got=route_signal(source,legs,1e-9)
    assert rec['discrete_ticks']==6
    assert np.all(got[:6]==0)
    assert got[6]==pytest.approx(.4)


def test_multihop_bound_at_least_geometrical_vacuum():
    rec=route_receipt([link(1,.8*C_M_PER_S),link(2,.6*C_M_PER_S)],1e-9)
    assert rec['continuous_front_delay_s'] >= rec['fastest_vacuum_arrival_s']
    assert rec['conservative_sampled_arrival_s'] >= rec['continuous_front_delay_s']
    assert rec['overshoot_s']<2e-9


def test_dissipative_single_path_not_energy_source():
    rng=np.random.default_rng(4);x=rng.normal(size=200)
    y=delayed_samples(x,link(1,.8*C_M_PER_S,.7),1e-9)
    assert np.dot(y,y)<=.49*np.dot(x,x)+1e-10


def test_higher_frequency_increases_phase_delay():
    x=link(.5,.7*C_M_PER_S)
    assert quasistatic_scale(x,1e8)['omega_tau_rad'] > quasistatic_scale(x,20e3)['omega_tau_rad']


def test_invalid_signal_frequency_rejected():
    with pytest.raises(ValueError):quasistatic_scale(link(),-1.)


def test_no_source_precursor_from_arbitrary_waveform():
    src=np.zeros(20);src[5:8]=[2.,-3.,1.]
    y=delayed_samples(src,link(C_M_PER_S*2e-9,C_M_PER_S),1e-9)
    assert np.all(y[:7]==0)
    assert y[7]==2.


def test_coarse_rotor_step_cannot_resolve_nanoscale_flight():
    z=run()
    assert z['existing_180_steps_per_rev_step_s']>10000*z['example_half_meter_cable']['length_m']/C_M_PER_S
    assert z['pwm_phase_scale']['omega_tau_rad']<.01


def test_zero_or_negative_sampling_dt_rejected():
    with pytest.raises(ValueError):link().flight_ticks(0.)
    with pytest.raises(ValueError):link().flight_ticks(-1.)


def test_route_requires_edges():
    with pytest.raises(ValueError):route_receipt([],1e-9)
