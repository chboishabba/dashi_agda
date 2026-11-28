"""Endpoint-first acceptance with original single-wave and switched ADE donors.
Run with Python/SymPy; no physical admission.
"""
import sympy as S
from solar_endpoint_inverse_fibre import *
from solar_gauss_ade_weld import incidence,augmented_step
from itertools import combinations

def run():
    assert fixed_source_headroom(1,S.Rational(4,5),S.Rational(1,4),S.Rational(1,100))['empty']
    assert not fixed_source_headroom(1,S.Rational(1,2),S.Rational(1,4),S.Rational(1,4))['empty']
    for a in [S.Rational(1,4),S.Rational(8,9),S.Integer(1)]:
        u,v=source_match(a);assert S.simplify(u*v)==1
        assert all(S.simplify(4*x/(1+x)**2-a)==0 for x in (u,v))
    assert not source_match(S.Rational(101,100))
    r=S.Matrix([1,S.I]);assert modal_projection(2*r,r)['unity_overlap']
    assert modal_projection(S.conjugate(r),r)['overlap']==0
    assert not modal_projection(S.zeros(2,1),r)['unity_overlap']
    A=S.Matrix([[1,1],[S.I,S.I]]);b=S.Matrix([2,2*S.I]);G=S.diag(1,3)
    f=minimum_cost_fibre(A,b,G);assert f['control']==S.Matrix([S.Rational(3,2),S.Rational(1,2)]) and f['minimum_cost']==3
    assert minimum_cost_fibre(A,S.Matrix([2,-2*S.I]),G)['status']=='EMPTY_EXACT_LINEAR_FIBRE'
    assert not selection([(1,0,0),(-1,0,0)],(0,1,0),2)
    assert selection([(1,1,1),(-1,0,-1)],(0,1,0),2)
    assert not selection([(1,1,1),(-1,0,2)],(0,1,0),2)
    # Free nonzero periodic initial state, joint observations.
    maps=[(S.Matrix([[S.Rational(1,2)]]),S.ones(1)),(S.Matrix([[S.Rational(1,2)]]),S.ones(1))]
    obs=[(S.ones(1),S.zeros(1))]*2
    f=periodic_inverse(maps,obs,S.Matrix([2,2]),S.eye(2));assert f['control']==S.ones(2,1) and f['minimum_cost']==2
    # Singular conserved coordinate; impossible inconsistent observations.
    maps=[(S.eye(1),S.zeros(1))]*2
    f=periodic_inverse(maps,obs,S.Matrix([2,3]),S.eye(2));assert f['status']=='EMPTY_EXACT_LINEAR_FIBRE'
    f=periodic_inverse(maps,obs,S.Matrix([2,2]),S.eye(2));assert f['initial']==S.Matrix([2]) and f['minimum_cost']==0
    # Rectangular original incidence switched ADE: two distinct endpoint mass maps.
    d=incidence([list(combinations(range(3),k)) for k in (1,2,3,4)])
    n=10;z=S.zeros(n,1);u=S.eye(3)[:,0];v=S.zeros(3,1)
    h=S.Rational(1,5);one=[S.Integer(1)]*3;two=[S.Integer(2)]*3;mb=[S.Integer(1)]
    args=(S.Integer(2),S.Integer(3),S.Rational(1,2),S.Rational(1,4),S.Rational(1,3))
    a=augmented_step(d,one,two,mb,*args,z,u,v,h)
    b=augmented_step(d,two,one,mb,*args,z,v,u,h)
    maps=[(a['T'],a['F']),(b['T'],b['F'])]
    O=S.zeros(1,n);O[0,0]=1;D=S.zeros(1,3)
    f=periodic_inverse(maps,[(O,D)]*2,S.Matrix([1,2]),S.eye(6))
    assert f['status']=='INHABITED'
    # Reopen the SAME periodic trajectory with signed actual work, not proxy.
    aa=augmented_step(d,one,two,mb,*args,f['initial'],v,f['control'][:3,:],h)
    bb=augmented_step(d,two,one,mb,*args,aa['state'],v,f['control'][3:,:],h)
    assert zero(bb['state']-f['initial'])
    assert S.simplify(sum(x['useful']+x['loss']-x['controller']-x['modulation'] for x in [aa,bb]))==0
    print(dict(status='ENDPOINT_INVERSE_FIBRE_PASS',ade_control_proxy=str(f['minimum_cost']),
               ade_source_off_net=str(S.simplify(sum(x['useful']-x['controller']-x['modulation'] for x in [aa,bb]))),
               physical_admission=False))
if __name__=='__main__':run()
