"""Magnetic/torque-first regression and falsifying controls; no V2 device data."""
import math
from dataclasses import replace
import pytest
from v2_omega_magnetic_torque_priority import (Magnetic,profile,evaluate,certified_envelope,
    exact_diamond_optimum,matched_electrical_load,magnetic_interventions,phase_number_negative_control,
    finite_voltage_candidates)

@pytest.mark.parametrize('u,v',[(0,0),(.6,0),(0,.6),(.3,.45),(-.6,0),(0,-.6),(.35,-.4),(.75,0)])
def test_exact_spectral_torque_matches_quadrature(u,v):
    r=evaluate(Magnetic(),u,v)
    assert abs(r['torque_integral_residual_w'])<1e-9
    assert abs(r['coenergy_identity_residual_w'])<1e-9
    assert abs(r['raw_bus_w']-r['exact_bus_w'])<1e-9
    assert r['storage_endpoint_delta_j']==0

@pytest.mark.parametrize('u,v',[(0,0),(.6,0),(0,.6),(.3,.45),(-.6,0)])
def test_continuous_voltage_lipschitz_bound(u,v):
    m=Magnetic();r=evaluate(m,u,v,n=4096)
    bound=r['continuous_envelope']['continuous_voltage_by_grid_lipschitz_v']
    # independent denser sampling is dominated by a proven derivative bound.
    dense=evaluate(m,u,v,n=16384)
    assert dense['peak_voltage_v']<=bound+1e-10
    assert r['continuous_envelope']['guaranteed_voltage_feasible_grid']
    assert r['continuous_envelope']['guaranteed_current_feasible']


def test_unmodulated_current_cannot_extract_mean_shaft_work():
    x=evaluate(Magnetic(),0,0)
    assert abs(x['shaft_exact_w'])<1e-12
    assert x['exact_bus_w']==-25.0


def test_reverse_timing_changes_generator_into_motor():
    x=evaluate(Magnetic(),.6,0);y=evaluate(Magnetic(),-.6,0)
    assert x['shaft_exact_w']>0>y['shaft_exact_w']
    assert abs(x['shaft_exact_w']+y['shaft_exact_w'])<1e-12


def test_negative_incremental_inductance_rejected():
    with pytest.raises(ValueError,match='inductance'):Magnetic(L0=.01).check()


def test_modulation_envelope_rejected():
    with pytest.raises(ValueError):evaluate(Magnetic(),.6,.6)


def test_torque_harmonics_vanish_if_geometry_vanishes():
    r=evaluate(Magnetic(a=0,b=0),.6,0)
    assert r['shaft_exact_w']==0


def test_nonlinear_saturation_does_not_fake_torque_gain():
    a=evaluate(Magnetic(beta=0),.3,.45)
    b=evaluate(Magnetic(beta=.00008),.3,.45)
    assert abs(a['shaft_exact_w']-b['shaft_exact_w'])<1e-12
    assert abs(a['peak_voltage_v']-b['peak_voltage_v'])>1e-2


def test_second_harmonic_changes_optimal_placement():
    x=exact_diamond_optimum(Magnetic(a=.012,b=0))
    y=exact_diamond_optimum(Magnetic(a=.012,b=.008))
    assert (x['u'],x['v'])==(.75,0)
    assert (y['u'],y['v'])==(0,.75)


def test_analytic_diamond_bound_and_sampled_grid():
    m=Magnetic();b=exact_diamond_optimum(m)['upper_bound_shaft_w']
    f=finite_voltage_candidates(m,step=.15,n=1024)
    assert f['candidate_count']>0 and f['feasible_count']>0
    assert f['best_feasible_sampled']['shaft_exact_w']<=b+1e-9


def test_equal_rms_not_equal_torque():
    r=magnetic_interventions(Magnetic())['rows']
    assert r['first_harmonic']['copper_w']==r['second_harmonic']['copper_w']
    assert r['first_harmonic']['shaft_exact_w']<r['second_harmonic']['shaft_exact_w']


def test_fixed_load_shaft_saving_equals_copper_saving():
    x=matched_electrical_load(Magnetic())
    assert abs(x['matched_output_shaft_saving_w']-x['matched_output_copper_saving_w'])<1e-10
    assert x['matched_output_shaft_saving_w']>14
    for r in x['arms'].values():
        assert abs(r['exported_bus_w']-20)<1e-9
        assert r['continuous_envelope']['guaranteed_voltage_feasible_grid']
        assert r['continuous_envelope']['guaranteed_current_feasible']


def test_motor_input_does_not_stay_constant_for_same_output():
    x=matched_electrical_load(Magnetic())
    assert x['arms']['first_harmonic']['incremental_motor_input_w']>x['arms']['cooperative_mix']['incremental_motor_input_w']>20


def test_hypothetical_motor_loss_model_can_be_disabled():
    m=Magnetic(motor_torque_loss_coeff=0)
    x=matched_electrical_load(m)
    for r in x['arms'].values():
        assert abs(r['incremental_motor_input_w']-r['shaft_exact_w'])<1e-9


def test_phase_count_baseline_no_magic():
    rows=phase_number_negative_control(Magnetic())
    assert len({round(x['total_shaft_w'],10) for x in rows.values()})==1
    assert rows['3']['net_w_with_0_1W_phase_overhead']>rows['9']['net_w_with_0_1W_phase_overhead']


def test_impossible_fixed_load_export_rejected():
    with pytest.raises(ValueError):matched_electrical_load(Magnetic(),target_bus_w=-1)


def test_current_ceiling_is_checked_independently():
    q=evaluate(Magnetic(peak_I=4.0,beta=.0001),0,.6)
    assert not q['continuous_envelope']['guaranteed_current_feasible']
