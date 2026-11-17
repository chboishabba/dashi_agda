"""Exact original source-owned heterogeneous Maxwell/ADE edge ↔ indexed face
identity and oriented Cayley midpoint tests. No calibrated physical face.
"""
from dataclasses import replace
import pytest
import sympy as S
from smith_filsinger_local_causal_ade_sympy import (
    local_spec,edge_updates,cayley_edge_step,source_kick,
    verified_dependency_trace)
from smith_filsinger_lorentz_ade_sympy import LorentzMaterial

def certified_face_edge(edge,original_face):
    """A two-endpoint face must use the SAME oriented original stage IDs."""
    _,i,j,a,b=edge
    if i==j:
        raise ValueError('diagonal scalar step not a two-endpoint Maxwell face')
    if original_face['source']==original_face['target']:
        raise ValueError('self-loop prohibited')
    if (original_face['source'],original_face['target'])!=(i,j):
        raise ValueError('face/field endpoint identity mismatch')
    return a,b

@pytest.mark.parametrize('n',[2,3,4,5])
def test_original_heterogeneous_offdiagonal_edge_ids_and_midpoint(n):
    mats=[replace(LorentzMaterial(),eps=S.Rational(i+2,3),
       mu=S.Rational(i+4,3),alpha=S.Rational(i+3,2),
       omega0sq=S.Rational(i+5,2)) for i in range(n)]
    spec=local_spec(n,layers=mats)
    z=S.Matrix([S.Rational(k+1,13) for k in range(4*n)])
    for face_index,edge in enumerate(edge_updates(spec)):
        _,i,j,a,b=edge
        if i==j:continue
        face={'id':face_index,'source':i,'target':j,'work':0}
        assert certified_face_edge(edge,face)==(a,b)
        h=S.Rational(1,11);p=h*a/2;r=h*b/2;q=1/(1-p*r)
        u=q*((1+p*r)*z[i]+(p+p)*z[j])
        v=q*((r+r)*z[i]+(1+p*r)*z[j])
        after=cayley_edge_step(spec,z,edge,h)['z']
        assert S.factor(after[i]-u)==0
        assert S.factor(after[j]-v)==0
        assert S.factor(u-p*v-(z[i]+p*z[j]))==0
        assert S.factor(v-r*u-(z[j]+r*z[i]))==0
        assert all(after[k]==z[k] for k in range(4*n) if k not in (i,j))

def test_reverse_original_face_is_not_same_oriented_update():
    spec=local_spec(3)
    edge=next(e for e in edge_updates(spec) if e[0]=='curl' and e[1]!=e[2])
    _,i,j,_,_=edge
    with pytest.raises(ValueError,match='mismatch'):
        certified_face_edge(edge,{'source':j,'target':i})

def test_concurrent_different_face_or_self_loop_rejected():
    spec=local_spec(3)
    edge=next(e for e in edge_updates(spec) if e[0]=='curl')
    _,i,j,_,_=edge
    with pytest.raises(ValueError,match='self-loop'):
        certified_face_edge(edge,{'source':i,'target':i})
    with pytest.raises(ValueError,match='mismatch'):
        certified_face_edge(edge,{'source':i,'target':j+10})

def test_diagonal_loss_not_mislabeled_as_maxwell_face():
    spec=local_spec(2,load=S.Rational(1,5))
    edge=next(e for e in edge_updates(spec) if e[0]=='ohmic')
    with pytest.raises(ValueError,match='diagonal'):
        certified_face_edge(edge,{'source':edge[1],'target':edge[2]})

def test_original_source_root_and_indexed_edge_in_sequence():
    spec=local_spec(3)
    edge=next(e for e in edge_updates(spec) if e[0]=='curl' and e[1]==2)
    start=S.zeros(12,1)
    first=source_kick(spec,start,2,S.Rational(3,2),origin='natural')
    step=cayley_edge_step(spec,first['z'],edge,S.Rational(1,7))
    receipt=verified_dependency_trace(start,[first,step])
    assert receipt['all_outside_zero']
    assert set(step['support']).issubset(receipt['cone'])
    assert not receipt['original_source_meter']
    assert not receipt['physical_maxwell_front']
