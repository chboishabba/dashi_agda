"""Native spherical structural atlas and one-sided material path, synthetic data."""
import numpy as np
from solar_spherical_cycle import geometry
from solar_spherical_material_weld import construct,structural_stage_atlas
from solar_material_generator_jvp import amplitude_material_boundary_jvp

def run():
    radii=[1.,1.2];level=0
    vol,mesh,ne,nf=geometry(radii,level);n=len(vol)
    assert n==24
    q=np.zeros((n,3));dq=q.copy();dq[0,:2]=[1.,.5]
    nu=np.full((n,3),.4);dnu=np.zeros_like(nu)
    gyro=np.tile([1.,-.5,.25],(n,1))
    axis=np.tile([0.,0.,1.],(n,1))
    def model(a): return construct(radii,level,np.arange(n),vol,a*a,nu,gyro,axis)
    base=model(q)
    pairs=structural_stage_atlas(base,mesh)
    full=model(np.ones_like(q))
    assert pairs==structural_stage_atlas(full,mesh)
    site=np.asarray(mesh['coordinate_site'])
    actual=set((int(i),int(j)) for i,j in zip(*np.nonzero(np.triu(full['generator'],1))) if site[i]!=site[j])
    assert set(pairs)==actual
    boundary=amplitude_material_boundary_jvp(base,vol,q,dq,nu,dnu,gyro,axis,dq>0)
    P=boundary['right_limit'];A=boundary['d_right_generator']
    assert np.any(P!=base['generator'])
    assert np.array_equal(A,-A.T)
    for eps in (.01,.001,.0001):
        candidate=model(q+eps*dq)
        assert np.allclose(candidate['generator'],P+eps*A,rtol=1e-12,atol=1e-12)
        assert np.array_equal(candidate['loss'],boundary['right_loss'])
        assert structural_stage_atlas(candidate,mesh)==pairs
    try: amplitude_material_boundary_jvp(base,vol,q,dq,nu,dnu,gyro,axis,q>0)
    except ValueError: pass
    else: raise AssertionError('missing right support admitted')
    print(dict(status='NATIVE_SPHERICAL_MATERIAL_ATLAS_PASS',cells=n,pairs=len(pairs),
               physical_admission=False))

if __name__=='__main__': run()
