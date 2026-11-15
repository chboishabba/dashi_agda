"""Original-claim independent physical model tests with fail-closed controls."""
import math
import sys
from dataclasses import replace
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
from v2_coupled_pulse_machine_maxcut import (
    Machine,magnetic,matrices,simulate,majorant,dominates,frontier,
    fixed_shaft_comparison,
)


def test_strict_passive_differential_inductance():
    p=Machine()
    for m in (3,6,9):
        L,dL,_=matrices(p,m,.37)
        eig=np.linalg.eigvalsh(L)
        assert min(eig)>0
        i=np.linspace(-5,5,m);z=np.linspace(.3,-.3,m)
        a=magnetic(p,i,z,.37)
        assert min(np.linalg.eigvalsh(a['incremental']))>=min(eig)-1e-12
        assert a['energy_j']>=0


def test_magnetic_energy_matches_its_legendre_transform():
    p=Machine()
    i=np.array([2.,-1.5,3.]);z=np.array([1.,-.5,1.7])
    r=magnetic(p,i,z,.9)
    assert np.isclose(r['energy_j'],i@r['flux']-r['coenergy_j'])
    # Flux is partial derivative of the scalar coenergy, not arbitrary constitutive data
    eps=1e-5
    for j in range(len(i)):
        shift=np.eye(len(i))[j]*eps
        grad=(magnetic(p,i+shift,z,.9)['coenergy_j']-magnetic(p,i-shift,z,.9)['coenergy_j'])/(2*eps)
        assert np.isclose(grad,r['flux'][j],rtol=1e-9,atol=1e-8)


def test_positive_nonnegative_magnetic_lag_dissipation():
    p=Machine()
    i=np.array([2.,-3.,.5]);z=np.array([1.,-1.,.2])
    f=p.lag_flux_h*i-p.lag_energy_h*z
    zd=p.lag_mobility*f
    assert np.dot(f,zd)>=0
    assert np.isclose(np.dot(f,zd),p.lag_mobility*np.dot(f,f))


@pytest.mark.parametrize('m,q,lead',[(3,0,0),(3,.45,.18),(4,.45,.18),
                                    (5,.45,.18),(6,.45,.18),(9,.45,.18)])
def test_independent_energy_and_temperature_endpoints(m,q,lead):
    r=simulate(Machine(),m,7,q,lead,True)
    assert r['feasible']
    assert abs(r['energy_residual_j'])<8e-5
    assert abs(r['bus_energy_residual_j'])<8e-5
    assert abs(r['thermal_energy_residual_j'])<1e-8
    assert r['max_voltage_v']<=Machine().bus_v
    assert r['max_current_continuous_majorant_a']<=Machine().current_limit_a
    assert r['thermal_continuous_majorant_c']<=Machine().thermal_limit_c
    assert r['switch_events']>0


def test_passive_regeneration_efficiency_increases_net_bus_work():
    a=Machine(eta_reverse=.8)
    b=replace(a,eta_reverse=1.)
    old=simulate(a,3,7,.45,.18,True)
    new=simulate(b,3,7,.45,.18,True)
    assert new['gross_regen_w']==old['gross_regen_w']
    assert new['power_mechanical_extract_w']==old['power_mechanical_extract_w']
    assert new['power_bus_w']>old['power_bus_w']
    assert math.isclose(new['power_bus_w']-old['power_bus_w'],
                        .2*old['gross_regen_w'],rel_tol=1e-9,abs_tol=1e-8)


def test_increased_switch_overhead_can_cancel_the_gain():
    p=Machine()
    base=simulate(p,3,7,.45,.18,True)
    bad=simulate(replace(p,switching_fixed_j=.08),3,7,.45,.18,True)
    # Extra switching heat slightly increases resistance and therefore also
    # perturbs the current trajectory: a physical feedback, not test equality.
    assert abs(base['power_mechanical_extract_w']-bad['power_mechanical_extract_w'])<.1
    assert bad['power_bus_w']<base['power_bus_w']
    assert abs(bad['energy_residual_j'])<8e-5


def test_fail_closed_invalid_positivity_and_thermal_conditions():
    for p in (Machine(l0_h=.001),Machine(eta_reverse=1.02),Machine(thermal_limit_c=20)):
        with pytest.raises(ValueError): simulate(p,3,5,.2,.1,True)
    assert not simulate(Machine(current_limit_a=1.),3,7,.45,.18,True)['feasible']


def test_continuous_current_majorant_really_bounds_short_numerical_motion():
    p=Machine()
    i=np.array([1.,2.,-3.]);z=np.array([.1,1.,-1.])
    a=majorant(p,i,z,2*math.pi/p.omega/p.steps_per_rev,3)
    assert a>max(np.abs(i).max(),np.abs(z).max())


def test_exact_enumerated_pareto_non_dominance():
    p=Machine()
    rows=[simulate(p,m,7,q,.18,True) for m in (3,4,5,6) for q in (0,.45)]
    pareto=frontier(rows)
    assert pareto
    assert not any(dominates(a,b) for b in pareto for a in rows if a is not b)
    assert all(any(r is candidate for candidate in pareto)
               or any(dominates(y,r) for y in rows if y is not r)
               for r in rows if r['feasible'])


def test_matched_shaft_is_explicit_selection_not_fixed_current():
    rows=fixed_shaft_comparison(Machine(),120,m_values=(3,5,6))
    assert len(rows)==3
    assert all(r['shaft_within_5pct'] for r in rows)
    assert all(abs(r['power_mechanical_extract_w']-120)<=6 for r in rows)
    assert len({round(r['peak_a'],2) for r in rows})>1


def test_counterfactual_no_lag_eliminates_memory_loss():
    p=replace(Machine(),lag_flux_h=0.,lag_energy_h=0.)
    r=simulate(p,3,7,.45,.18,True)
    assert abs(r['power_hysteresis_w'])<1e-12
    assert abs(r['energy_residual_j'])<8e-5


def test_storage_endpoint_negative_control_blocks_false_winner():
    # Same numerical electrical result can look attractive when the inductor
    # reservoir is being depleted. It MUST NOT be reported as sustainable.
    p=Machine()
    five=simulate(p,5,4.75,.45,.18,True)
    three=simulate(p,3,6.,.45,.18,True)
    assert five['power_bus_w']>three['power_bus_w']
    assert five['power_storage_change_w']< -40
    assert five['storage_adjusted_bus_w']<three['storage_adjusted_bus_w']
    assert not five['magnetically_periodic_2pct']
    assert math.isclose(five['storage_adjusted_bus_w'],
                        five['power_bus_w']+five['power_storage_change_w'],abs_tol=1e-12)


def test_exact_symbolic_nonlin_multiport_memory_identity():
    from v2_coupled_pulse_machine_maxcut import symbolic_multicoil_identity
    assert symbolic_multicoil_identity()['residual']=='0'


@pytest.mark.parametrize('m', (3,5,6,9,12))
def test_pwm_average_has_approximately_matched_magnetic_state_after_warmup(m):
    # A distinct averaged-PWM controller intentionally gives a POSITIVE
    # near-periodic control, not proof of actual high-frequency switch ripple.
    p=replace(Machine(),warmup_revs=5)
    r=simulate(p,m,14,.45,.18,True,controller_mode='pwm_tracking')
    assert r['feasible']
    assert r['magnetically_periodic_2pct']
    assert abs(r['power_storage_change_w'])<.01
    assert r['max_voltage_v']<=p.bus_v+1e-12
    assert abs(r['energy_residual_j'])<8e-5
    assert abs(r['thermal_energy_residual_j'])<1e-8


def test_pwm_average_mixed_phase_ripple_efficiency_pareto_tradeoff():
    p=replace(Machine(),warmup_revs=5)
    three=simulate(p,3,14,.45,.18,True,controller_mode='pwm_tracking')
    nine=simulate(p,9,14,.45,.18,True,controller_mode='pwm_tracking')
    assert abs(three['power_mechanical_extract_w']-nine['power_mechanical_extract_w'])<2
    assert three['power_bus_w']>nine['power_bus_w']
    assert nine['torque_ripple']<three['torque_ripple']
    assert three['magnetically_periodic_2pct'] and nine['magnetically_periodic_2pct']
