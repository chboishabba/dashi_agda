#!/usr/bin/env python3
"""Regression on finite LC/plasma source backaction; no original-world evidence."""
from dataclasses import replace
import pytest
from check_smith_filsinger_distributed_causal_energy import Model,run,symbolic_telescoping_check

def test_baseline_energy():
    r=run(Model(), duration=5.)
    assert abs(r['net_balance_residual'])<1e-7
    assert r['max_pointwise_residual']<1e-9

def test_density_response_paid():
    base=run(Model(),duration=5.)
    control=run(replace(Model(),ion_driven=.8,controller_aux=.02),duration=5.)
    assert control['channel_conductance']>base['channel_conductance']
    assert control['work']['ion_creation_paid']>base['work']['ion_creation_paid']
    assert abs(control['net_balance_residual'])<1e-7

def test_source_off_all_empty_no_electric_work():
    p=replace(Model(),exogenous_dc=0,exogenous_ac=0,ion_seed=0,n_init=0)
    r=run(p,duration=3.)
    assert abs(r['work']['upstream_input'])<1e-12
    assert abs(r['work']['load'])<1e-12

def test_source_depletion_not_natural_gain():
    p=replace(Model(),g_recharge=0,exogenous_dc=0,exogenous_ac=0,n_init=.2)
    r=run(p,duration=3.)
    assert r['work']['upstream_input']==0
    assert not r['storage_restored']

def test_bad_parameters_fail():
    with pytest.raises(ValueError):run(replace(Model(),c_node=-1))
    with pytest.raises(ValueError):run(replace(Model(),r_link=-.2))

@pytest.mark.parametrize('nodes',[3,5,8])
def test_multiple_spatial_sizes(nodes):
    p=replace(Model(),nodes=nodes,plasma_node=nodes//2)
    r=run(p,duration=3.)
    assert abs(r['net_balance_residual'])<1e-7

@pytest.mark.parametrize('nodes',[3,5,8])
def test_general_discrete_chain_symbolic_energy(nodes):
    assert symbolic_telescoping_check(nodes)

def test_more_conductance_can_reduce_useful_load():
    baseline=run(Model(),duration=10.)
    controlled=run(replace(Model(),ion_driven=.8,controller_aux=.02),duration=10.)
    assert controlled['channel_conductance']>baseline['channel_conductance']
    assert controlled['work']['load']<baseline['work']['load']
    assert controlled['net_useful_after_control_and_ionization']<baseline['net_useful_after_control_and_ionization']
