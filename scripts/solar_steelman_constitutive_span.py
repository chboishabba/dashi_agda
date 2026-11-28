"""Exact coefficient-space constitutive inverse on the actual loaded orbit.
Frozen lossless skew law, passive damping, and paid residual distinguished.
No physical material identification is inferred from an algebraic witness.
"""
import sympy as S
from solar_coherent_reverse_weld import reverse_ports

def pack_harmonics(v):
    return S.Matrix.vstack(*[part for w in (1,2) for part in v[w]])

def skew_basis(d):
    for i in range(d):
        for j in range(i+1,d):
            K=S.zeros(d);K[i,j]=1;K[j,i]=-1
            yield K

def inverse_columns(z,r,basis):
    """One common real coefficient vector at both occupied bands."""
    d=len(z[1][0]);b=pack_harmonics(r)
    cols=[pack_harmonics({w:tuple(K*v for v in z[w]) for w in (1,2)}) for K in basis]
    A=S.Matrix.hstack(*cols) if cols else S.zeros(4*d,0)
    if not A.cols:
        return dict(control=S.zeros(0,1),residual=b,null_fibre=[],reachable=b==S.zeros(b.rows,1),physical_admission=False)
    # Reuse existing exact rectangular affine inverse, one step with zero
    # initial state. This is a coefficient-space calculation, not a time step.
    result=reverse_ports([(S.eye(A.rows),A)],S.eye(A.rows),S.zeros(A.rows,1),b)
    e=result['residual']
    assert A*result['control']+e==b and A.T*e==S.zeros(A.cols,1)
    assert S.expand(b.dot(e)-e.dot(e))==0
    return result

def local_inverse(a,full=False):
    reports=[]
    for ids,r,_ in a['models']:
        z={w:tuple(v[ids,:] for v in a['data'][w][0]) for w in (1,2)}
        d=len(ids)
        # RMS two-band inner product equals mean instantaneous z dot F.
        zz=pack_harmonics(z);rr=pack_harmonics(r)
        mean=zz.dot(rr)
        assert mean==a['means'][len(reports)]
        # Any instantaneous skew current-only law (even time-dependent)
        # has z dot K z=0, so nonzero mean excludes it outright.
        # Passive damping has nonpositive mean in this same force convention.
        # A positive mean requires another paid/reversible energy port.
        assert zz.dot(zz)>0 or mean==0
        lower=S.cancel(mean**2/zz.dot(zz)) if zz.dot(zz)>0 else S.Integer(0)
        rec=dict(cell=len(reports),d=d,mean=mean,skew_residual_lower_squared=lower)
        if full:
            result=inverse_columns(z,r,list(skew_basis(d)))
            e=result['residual'];rec['frozen_skew_reachable']=result['reachable']
            rec['frozen_skew_residual_squared']=e.dot(e)
            assert rec['frozen_skew_residual_squared']>=lower
        reports.append(rec)
    assert sum(r['mean'] for r in reports)==0
    assert any(r['mean']>0 for r in reports) and any(r['mean']<0 for r in reports)
    print('local current-only skew no-go count',sum(r['mean']!=0 for r in reports),flush=True)
    print('local passive damping no-go count',sum(r['mean']>0 for r in reports),flush=True)
    print('LIMIT signed mean no-go is for isolated current-only forces, not the existing paid shared-store mediator or a general nonlinear material')
    return reports

def fixture():
    z={1:(S.Matrix([1,0]),S.Matrix([0,1])),2:(S.Matrix([1,1]),S.Matrix([0,0]))}
    K=S.Matrix([[0,2],[-2,0]])
    r={w:tuple(K*v for v in z[w]) for w in (1,2)}
    assert inverse_columns(z,r,[K])['reachable']
    r[1]=(r[1][0]+z[1][0],r[1][1])
    res=inverse_columns(z,r,[K]);assert not res['reachable']
    assert res['residual'].dot(res['residual'])>0
    print('PASS exact span positive and negative fixture')

if __name__=='__main__':
    import argparse,pickle
    p=argparse.ArgumentParser();p.add_argument('--mediator');p.add_argument('--full',action='store_true');x=p.parse_args()
    fixture()
    if x.mediator:
        with open(x.mediator,'rb') as f:a=pickle.load(f)
        local_inverse(a,x.full)
