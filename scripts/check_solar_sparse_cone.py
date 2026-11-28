"""Byte-for-byte dense/sparse receipts on original indexed cone, all jets."""
import numpy as np
from scipy.sparse import csr_matrix
from solar_physical_cone import timed_step,fixtures

def run():
    mesh=dict(positions_m=[[0,0,0],[1,0,0],[2,0,0]],coordinate_site=[0,1,2],
        faces=[dict(id='a',source=0,target=1,normal=[1,0,0],area_m2=1),dict(id='b',source=1,target=2,normal=[1,0,0],area_m2=1)],front_speed_m_s=100.)
    H=np.diag([-.5,0.,0.]); P=H.copy();P[1,1]=-.25
    A1=np.zeros((3,3));A1[0,1]=-1;A1[1,0]=1;A1[1,2]=-2;A1[2,1]=2
    A2=np.zeros((3,3));A2[1,2]=-2;A2[2,1]=2
    port=np.array([.5,0.,0.]); inc=.2;force=2*inc*port
    forms=dict(source=np.outer(port,port),load=np.diag([.25,0.,0.]))
    x=np.array([1.,0.,0.]);z=np.zeros(3);atlas=((0,1),(1,2));seed=np.full((3,3),np.inf);seed[0,0]=0.
    ans=[]
    for sparse in (False,True):
        M=csr_matrix if sparse else np.asarray
        out=[];a=x.copy();b=z.copy();c=z.copy();reach=seed.copy()
        for step in range(2):
            a,r=timed_step(a,M(H),force,.25,mesh,{k:M(v) for k,v in forms.items()},port,inc,
                retain_local_midpoint=True,retain_stage_residuals=True,jvp=(b,M(A1),z),
                atlas_pairs=atlas,right_limit=M(P),jet2=(c,M(A2),z),reach_seed=reach,clock_start=step*.25)
            b=np.array(r['state_jvp']);c=np.array(r['state_coefficient2']);reach=np.array([[np.inf if v is None else v for v in r[k]] for k in ('arrival_s','directional_arrival_s','coefficient2_arrival_s')])
            assert r.pop('sparse_operator')==sparse;out.append(r)
        ans.append((a,b,c,out))
    for a,b in zip(ans[0][:3],ans[1][:3]):assert np.array_equal(a,b)
    assert ans[0][3]==ans[1][3]
    assert ans[0][3][-1]['coefficient2_arrival_s'][2] is not None
    # Omit required dormant tangent edge and give nonlocal loss: fail closed.
    for kwargs in (dict(atlas_pairs=((0,1),)),dict(loss_forms={'loss':csr_matrix([[.5,1,0],[1,0,0],[0,0,0]])})):
        base=dict(jvp=(z,csr_matrix(A1),z),atlas_pairs=atlas,right_limit=csr_matrix(P),jet2=(z,csr_matrix(A2),z))
        base.update(kwargs)
        try:timed_step(x,csr_matrix(H),force,.25,mesh,**base)
        except ValueError:pass
        else:raise AssertionError('invalid sparse atlas or loss admitted')
    assert fixtures()['short_clock_rejected']
    print(dict(status='SPARSE_CONE_PASS',steps=2,stage_receipts=len(ans[0][3][0]['events'])*2,
        exact_dense_sparse_state_parity=True,exact_receipt_parity=True,negative_controls=3))
if __name__=='__main__':run()
