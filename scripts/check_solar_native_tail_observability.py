"""Actual original right-limit occupied-space certificate and undamped control."""
import numpy as np
from solar_synthetic_fixture import fixture
from solar_changing_tail import right_limit_reference
from solar_tail_observability import reference_observability
from solar_spherical_geometry import geometry
from solar_physical_cone import timed_step
from solar_matrix_storage import diagonal

def run():
    m,c,_,_=fixture();c=dict(c,sparse_operator=True,kinetics=dict(c['kinetics'],ionization_s_inv=[0.,0.]))
    n=len(m[0]);pop=np.tile([5.,3.,2.],(n,1))
    r=right_limit_reference(m,c,pop);_,mesh,ne,nf=geometry(c['radii_m'],c['angular_level'])
    q=reference_observability(r['generator'],r['dt'],r['receipt'],r['occupied'],ne+nf)
    assert q['rank']==ne+nf==98 and q['occupied_size']==314 and q['strict_occupied_block_contraction']
    H=r['generator']+diagonal(np.r_[-float(r['generator'][0,0]),np.zeros(313)],True)
    _,rec=timed_step(np.zeros(314),H,np.zeros(314),r['dt'],mesh,atlas_pairs=r['atlas'])
    neg=reference_observability(H,r['dt'],rec,r['occupied'],98)
    assert neg['rank']==0 and not neg['strict_occupied_block_contraction']
    print(dict(status='NATIVE_TAIL_OBSERVABILITY_PASS',certificate=q,undamped_negative_control=True))
if __name__=='__main__':run()
