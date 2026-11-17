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
