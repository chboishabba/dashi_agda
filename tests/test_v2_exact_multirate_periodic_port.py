"""Finite causal packet / memory-machine exact certificate adversarial tests."""
from fractions import Fraction as F
from pathlib import Path
import importlib.util
import sys
import math
import numpy as np
import pytest
SRC=Path(__file__).resolve().parents[1]/'scripts'/'v2_exact_multirate_periodic_port.py'
spec=importlib.util.spec_from_file_location('v2_exact_port',SRC)
mod=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=mod
spec.loader.exec_module(mod)

@pytest.mark.parametrize('n',(1,2,3,4))
@pytest.mark.parametrize('s',(F(0),F(1,2),F(1)))
@pytest.mark.parametrize('g',(F(0),F(1,4)))
def test_rational_matrix_coefficient_identity_every_initial_state(n,s,g):
    p=mod.Params(n=n,s=s,g=g)
    M,Q,H=mod.one_step_certificate(p,F(1))
    d=2*n+3
    assert len(M)==d
    assert len(H)==d
    assert set(Q)=={'source','motor_port','line_loss','copper','memory'}
    x=[F(1,5)]* (d-1)
    xp,r=mod.step(p,F(1),x,F(-1,3))
    assert r['balance']==0 and r['line_motor_port_balance']==0
    assert xp==mod.mv(M,x+[F(-1,3)])[:-1]

@pytest.mark.parametrize('k',(0,1,2,3,5,8,12,16))
@pytest.mark.parametrize('n',(1,2,3))
def test_binary_exact_work_matches_every_microscopic_tick(n,k):
    p=mod.Params(n=n)
    x=[F(i-3,7) for i in range(2*n+2)]
    u=F(2,5)
    end,receipts=mod.fraction_receipts(p,F(5,4),x,u,k)
    expected,totals=mod.explicit_steps(p,F(5,4),x,u,k)
    assert end==expected
    for key in totals:
        assert receipts[key]==totals[key],(n,k,key)
    assert receipts['energy_residual']==0

@pytest.mark.parametrize('n',(1,2,3))
@pytest.mark.parametrize('block',(1,2,3))
def test_exact_clocked_reluctance_periodic_unique_attractor(n,block):
    p=mod.Params(n=n)
    r=mod.periodic_certificate(p,block_length=block)
    assert r['period_energy_residual']=='0'
    assert F(r['contraction_inf_norm'])<1
    assert len(r['fixed_state_fraction'])==2*n+2
    assert r['memory_loss_float']>0
    assert r['copper_loss_float']>0
    assert r['line_loss_float']>0
    assert abs(r['source_work_float']+r['local_mechanical_work_float']
               -r['copper_loss_float']-r['memory_loss_float']-r['line_loss_float'])<1e-14

@pytest.mark.parametrize('n',(1,2,3,4))
def test_strict_positive_oneway_and_round_trip_nonanticipation(n):
    p=mod.Params(n=n)
    x0=[F(0)]*(2*n+2)
    pulse=x0[:];quiet=x0[:]
    remote=[];returned=[]
    for k in range(2*n+3):
        current_incident=p.s*pulse[n-1]
        quiet_incident=p.s*quiet[n-1]
        remote.append(current_incident-quiet_incident)
        returned.append(p.s*(pulse[n]-quiet[n]))
        pulse,_=mod.step(p,F(1),pulse,F(1) if k==0 else F(0))
        quiet,_=mod.step(p,F(1),quiet,F(0))
    assert all(v==0 for v in remote[:n])
    assert remote[n]!=0
    assert all(v==0 for v in returned[:2*n])
    assert returned[2*n]!=0

@pytest.mark.parametrize('kwargs',[
    {'n':0},{'dt':F(0)},{'Z':F(0)},{'R':F(0)},{'h':F(0)},
    {'s':F(5,4)},{'s':F(-1,4)},
    {'front_m_s':F(mod.C0+1)},{'front_m_s':F(-1)}
])
def test_invalid_parameter_rejected(kwargs):
    with pytest.raises(ValueError):mod.Params(**kwargs).check()

def test_energy_requires_signed_external_rotor_modulation():
    p=mod.Params()
    r=mod.periodic_certificate(p)
    assert F(r['local_mechanical_work'])!=0
    # Omitting the mechanical term would leave precisely that residual.
    assert F(r['source_work'])-F(r['line_loss'])-F(r['copper_loss'])-F(r['memory_loss'])==-F(r['local_mechanical_work'])

def test_no_arbitrary_passive_port_gain():
    p=mod.Params()
    x=[F(0)]*(2*p.n+2)
    end,r=mod.fraction_receipts(p,F(1),x,F(0),100)
    assert all(v==0 for v in end)
    for key in ('source','line_loss','copper','memory','motor_port','energy_change'):
        assert r[key]==0

def test_fast_very_long_line_block_respects_work_and_natural_flight():
    r=mod.long_cable_microtick_example()
    assert r['microticks_for_2354rpm_period']>10_000_000
    assert math.isclose(r['cable_m'],.5,rel_tol=1e-12)
    assert r['flight_s']>0
    assert abs(r['work_j']['energy_residual'])<2e-9
    assert r['work_j']['copper']>=0 and r['work_j']['memory']>=0
    assert r['work_j']['line_loss']>=0

@pytest.mark.parametrize('k',(1,2,7,20,96))
def test_floating_binary_superstep_matches_exact_rational_block(k):
    p=mod.Params(n=2)
    x=[F(1,8),F(-1,6),F(3,11),F(-2,13),F(1,5),F(-1,7)]
    u=F(3,5)
    ex,exact=mod.fraction_receipts(p,F(3,4),x,u,k)
    got,approx=mod.float_receipts(p,F(3,4),x,u,k)
    assert np.allclose([float(a) for a in ex],got,rtol=2e-11,atol=1e-12)
    for key in ('source','motor_port','line_loss','copper','memory','energy_change'):
        assert math.isclose(float(exact[key]),approx[key],rel_tol=5e-10,abs_tol=1e-11)
    assert abs(approx['energy_residual'])<1e-10

def test_fast_semigroup_does_not_advance_front_early():
    p=mod.Params(n=3)
    x=[F(0)]*(2*p.n+2)
    # After only two microscopic ticks, there is no remote flux response.
    out2,_=mod.fraction_receipts(p,F(1),x,F(1),2)
    assert out2[-2]==0
    out3,_=mod.fraction_receipts(p,F(1),x,F(1),3)
    assert out3[-2]==0
    out4,_=mod.fraction_receipts(p,F(1),x,F(1),4)
    assert out4[-2]!=0

def test_source_and_rotor_parameter_events_must_not_be_merged():
    p=mod.Params()
    x=[F(0)]*(2*p.n+2)
    y1,_=mod.fraction_receipts(p,F(1),x,F(1),2)
    y2,_=mod.fraction_receipts(p,F(3,4),y1,F(-1),2)
    wrong,_=mod.fraction_receipts(p,F(1),x,F(1),4)
    assert y2!=wrong

@pytest.mark.parametrize('bad',(-1,1.01,0))
def test_physical_speed_ratio_fails_closed(bad):
    with pytest.raises(ValueError):mod.physical_delay_bound(speed_ratio=bad)

def test_fraction_energy_ledger_includes_negative_motor_port():
    p=mod.Params()
    x=[F(0)]*(2*p.n)+[F(1),F(0)]
    new,row=mod.step(p,F(1),x,F(0))
    assert row['motor_port']<0
    assert row['balance']==0


def test_restricted_model_boundary_statements_explicit():
    r=mod.run()
    assert r['exact_matrix_all_states']
    assert len(r['not_proved'])>=4
    assert r['periodic_certificate']['period_energy_residual']=='0'
