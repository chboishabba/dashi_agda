"""Local exact acceptance of the same-cochain and coherent reverse weld."""
import sympy as S
from itertools import combinations
from solar_gauss_ade_weld import incidence,split_audit,augmented_step
from solar_coherent_reverse_weld import periodic,reverse_ports,harmonic_columns

def run():
    d=incidence([list(combinations(range(4),k)) for k in (1,2,3,4)])
    r=split_audit(d,[S.Integer(1)]*6,[S.Integer(1)]*4,S.Rational(1,3))
    assert r['physical_leakage']!=S.zeros(*r['physical_leakage'].shape)
    assert r['signed_split_defect']!=S.zeros(*r['signed_split_defect'].shape)
    # Exact closed tetrahedral complex, rectangular edge/face ADE.
    n=22;z=S.zeros(n,1);u=S.eye(6)[:,0];v=S.zeros(6,1)
    h=S.Rational(1,5);one=[S.Integer(1)]*6;two=[S.Integer(2)]*6;mb=[S.Integer(1)]*4
    args=(S.Integer(2),S.Integer(3),S.Rational(1,2),S.Rational(1,4),S.Rational(1,3))
    a=augmented_step(d,one,two,mb,*args,z,u,v,h)
    b=augmented_step(d,two,one,mb,*args,a['state'],v,u,h)
    assert a['natural']>0 and b['controller']!=0
    maps=[(a['T'],a['F']),(b['T'],b['F'])]
    st,M,ker=periodic(maps,[u,v]);assert st[0]==st[-1]
    # A desired magnetic divergence is impossible from these electric ports.
    O=S.zeros(1,n);O[:,6:10]=d[2]
    no=reverse_ports(maps,O,z,S.ones(1,1));assert not no['reachable'] and no['residual']==S.ones(1,1)
    yes=reverse_ports(maps,S.eye(n),z,b['T']*a['F']*u+b['F']*v);assert yes['reachable']
    H=harmonic_columns(maps,S.Integer(2),S.Integer(-1))
    assert H[:n,6:]!=S.zeros(n,6)
    print(dict(status='GAUSS_ADE_REVERSE_PASS',physical_dimension=r['physical_basis'].cols,
        split_defect_rank=r['signed_split_defect'].rank(),physical_leakage_rank=r['physical_leakage'].rank(),
        periodic_null_dimension=len(ker),harmonic_shape=H.shape,physical_admission=False))
if __name__=='__main__':run()
