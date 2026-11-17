"""Exact primitive-local Maxwell–Lorentz causality, source and loss tests."""
import pytest
import sympy as S
from smith_filsinger_local_causal_ade_sympy import (
    local_spec,edge_updates,cayley_edge_step,source_kick,source_response,
    dependency_step,dependency_cone,full_ledger)

@pytest.mark.parametrize('n',[1,2,3,4])
def test_each_primitive_lossless_or_paid(n):
    spec=local_spec(n,load=S.Rational(1,5))
    z=S.Matrix([S.Rational(i+1,7) for i in range(4*n)])
    for edge in edge_updates(spec):
        r=cayley_edge_step(spec,z,edge,S.Rational(1,7))
        assert r['energy_change']==r['work']
        if edge[0] in ('curl','polar_E_V','polar_P_V'):
            assert r['work']==0
        else:assert r['work']<=0
        for k in range(4*n):
            if k not in r['support']:assert r['z'][k]==z[k]

@pytest.mark.parametrize('n',[2,3,4])
def test_source_to_distant_sensor_requires_chain_of_local_couplings(n):
    spec=local_spec(n)
    edges=edge_updates(spec)
    response=source_response(spec,n-1,[],S.Rational(1,4))
    assert response['field'][0]==0 and 0 not in response['cone']
    sorted_edges=[edge for i in reversed(range(n)) for edge in edges
                  if edge[0]=='curl' and edge[1] in (i,i-1)]
    response=source_response(spec,n-1,sorted_edges,S.Rational(1,4))
    assert response['all_outside_zero']
    for k in range(4*n):
        if k not in response['cone']:assert response['field'][k]==0

def test_no_superluminal_inference_from_numerical_graph():
    spec=local_spec(4)
    out=source_response(spec,3,[],S.Rational(1,10000))
    assert out['cone']=={3}
    assert not out['records'][0].get('physical_maxwell_front',False)

def test_exact_source_controller_and_separate_dissipation():
    spec=local_spec(3,load=S.Rational(1,3))
    z=S.zeros(12,1);start=z;history=[]
    for cell,val,origin in ((2,S.Integer(3),'natural'),
                            (0,S.Rational(1,2),'controller')):
        r=source_kick(spec,z,cell,val,S.Rational(1,5),origin)
        history.append(r);z=r['z']
    for edge in edge_updates(spec):
        r=cayley_edge_step(spec,z,edge,S.Rational(1,5))
        history.append(r);z=r['z']
    ledger=full_ledger(spec,start,history)
    assert ledger['residual']==0
    assert ledger['natural']>0 and ledger['controller']>0
    assert ledger['useful_load']>0 and ledger['ohmic']>0
    assert ledger['relaxation']>=0
    assert not ledger['restored_all_states']
    assert not ledger['physical_source_meter']

def test_source_off_precharged_storage_is_not_replenishment():
    spec=local_spec(2,load=S.Rational(1,2))
    z=S.zeros(8,1);z[0]=2;initial=z;history=[]
    for edge in edge_updates(spec):
        step=cayley_edge_step(spec,z,edge,S.Rational(1,4))
        history.append(step);z=step['z']
    ledger=full_ledger(spec,initial,history)
    assert ledger['natural']==ledger['controller']==0
    assert ledger['useful_load']>0 and ledger['energy_change']<0
    assert not ledger['restored_all_states']

def test_forged_disconnected_history_rejected():
    spec=local_spec(2);zero=S.zeros(8,1)
    a=source_kick(spec,zero,0,1);b=source_kick(spec,zero,1,1)
    with pytest.raises(ValueError,match='nonconsecutive'):
        full_ledger(spec,zero,[a,b])

def test_wrong_source_owner_rejected():
    spec=local_spec(1)
    with pytest.raises(ValueError,match='source ownership'):
        source_kick(spec,S.zeros(4,1),0,1,origin='solar-certified')

def test_dependency_boolean_cone_is_local_and_monotone():
    assert dependency_step({0},(2,3))=={0}
    assert dependency_step({0},(0,1))=={0,1}
    assert dependency_cone(0,[{'support':(0,1)},{'support':(2,3)}])=={0,1}
    assert dependency_cone(0,[{'support':(0,1)},{'support':(1,2)}])=={0,1,2}

def test_global_implicit_matrix_inverse_has_remote_one_step_tail():
    from smith_filsinger_lorentz_ade_sympy import generator,exact_midpoint
    n=4;A,B,M=generator(n)
    source=S.zeros(n,1);source[n-1]=1
    result=exact_midpoint(S.zeros(4*n,1),source,S.zeros(n,1),
                          S.Rational(1,6),A,B,M)
    assert S.factor(result['z'][0])!=0
    local=source_response(local_spec(n),n-1,[],S.Rational(1,6))
    assert local['field'][0]==0 and 0 not in local['cone']

def test_wrong_load_makes_original_dissipation_ledger_fail():
    spec=local_spec(2,load=S.Rational(1,3))
    initial=S.zeros(8,1);hit=source_kick(spec,initial,0,1)
    loadedge=next(e for e in edge_updates(spec)
                  if e[0]=='useful_load' and e[1]==0)
    step=cayley_edge_step(spec,hit['z'],loadedge)
    ledger=full_ledger(spec,initial,[hit,step])
    assert ledger['residual']==0 and ledger['useful_load']>0
    assert S.factor(ledger['energy_change']-ledger['natural']) == -ledger['useful_load']


@pytest.mark.parametrize('n',[3,4,5])
def test_heterogeneous_soil_air_ionosphere_material_ports(n):
    from smith_filsinger_lorentz_ade_sympy import LorentzMaterial
    from dataclasses import replace
    base=LorentzMaterial()
    layers=[replace(base,eps=S.Rational(i+2,2),mu=S.Rational(i+3,2),
                    sigma=S.Rational(i+1,7),alpha=S.Rational(i+2,3),
                    gamma=S.Rational(i+1,5),omega0sq=S.Rational(i+4))
            for i in range(n)]
    spec=local_spec(n,layers=layers,load=S.Rational(1,3))
    assert spec['materials']==tuple(layers)
    z=S.Matrix([S.Rational(k+1,9) for k in range(4*n)])
    for edge in edge_updates(spec):
        step=cayley_edge_step(spec,z,edge,S.Rational(1,7))
        assert step['energy_change']<=0
        if edge[0] in ('curl','polar_E_V','polar_P_V'):
            assert step['energy_change']==0
        z=step['z']
    first=S.zeros(4*n,1);sourced=source_kick(spec,first,n-1,2)
    ledger=full_ledger(spec,first,[sourced])
    assert ledger['residual']==0 and ledger['natural']>0
    assert not ledger['physical_source_meter']

def test_missing_layer_or_negative_layer_damping_fail_closed():
    from smith_filsinger_lorentz_ade_sympy import LorentzMaterial
    from dataclasses import replace
    with pytest.raises(ValueError,match='one material per cell'):
        local_spec(3,layers=[LorentzMaterial()]*2)
    with pytest.raises(ValueError):
        local_spec(3,layers=[LorentzMaterial(),LorentzMaterial(),
          replace(LorentzMaterial(),gamma=-1)])


@pytest.mark.parametrize('second_cell',[0,1,2])
def test_later_disjoint_natural_source_is_new_dynamic_root(second_cell):
    from smith_filsinger_local_causal_ade_sympy import verified_dependency_trace
    spec=local_spec(3)
    z=S.zeros(12,1)
    first=source_kick(spec,z,2,1,origin='natural')
    second=source_kick(spec,first['z'],second_cell,1,origin='controller')
    trace=verified_dependency_trace(z,[first,second])
    assert trace['cone']=={2,second_cell}
    assert trace['stages'][0]==frozenset({2})
    assert trace['stages'][1]==frozenset({2,second_cell})
    assert dependency_cone(None,[first,second])=={2,second_cell}


def test_disconnected_stage_cannot_seed_an_unpaid_field():
    from smith_filsinger_local_causal_ade_sympy import verified_dependency_trace
    spec=local_spec(3)
    z=S.zeros(12,1)
    first=source_kick(spec,z,2,1)
    forged={'initial_state':first['z'], 'z':first['z'].copy(),
            'support':(0,3)}
    forged['z'][7]=S.Rational(1,2)
    with pytest.raises(ValueError,match='declared local support'):
        verified_dependency_trace(z,[first,forged])


def test_forged_source_ownership_or_untyped_step_rejected():
    from smith_filsinger_local_causal_ade_sympy import verified_dependency_trace
    spec=local_spec(2);z=S.zeros(8,1)
    with pytest.raises(ValueError,match='unknown source owner'):
        verified_dependency_trace(z,[{'initial_state':z,'z':z,
                                      'kind':'solar-certified','cell':0}])
    with pytest.raises(ValueError,match='untyped'):
        dependency_cone(None,[{'cell':1}])


def test_cone_expands_only_after_actual_scheduled_edge():
    from smith_filsinger_local_causal_ade_sympy import verified_dependency_trace
    spec=local_spec(3);z=S.zeros(12,1)
    first=source_kick(spec,z,2,1)
    edges=[e for e in edge_updates(spec) if e[0]=='curl']
    remote=next(e for e in edges if e[1]==0)
    stage=cayley_edge_step(spec,first['z'],remote)
    result=verified_dependency_trace(z,[first,stage])
    assert result['cone']=={2}
    assert all(stage['z'][k]==0 for k in range(12) if k!=2)


def test_forged_source_kick_cannot_modify_other_active_coordinate():
    from smith_filsinger_local_causal_ade_sympy import verified_dependency_trace
    spec=local_spec(3);z=S.zeros(12,1)
    first=source_kick(spec,z,2,1)
    second=source_kick(spec,first['z'],0,1,origin='controller')
    fake=dict(second)
    fake['z']=second['z'].copy()
    fake['z'][2]+=1
    with pytest.raises(ValueError,match='source kick violates local'):
        verified_dependency_trace(z,[first,fake])
