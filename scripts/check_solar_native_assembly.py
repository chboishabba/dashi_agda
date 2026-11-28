"""Actual original Whitney material assembly and indexed stage gate, no data imports."""
import numpy as np
from solar_spherical_geometry import geometry
from solar_spherical_material_weld import construct,structural_stage_atlas,_prepared_static_geometry
from solar_physical_cone import timed_step
from solar_matrix_storage import close

def run(depth=0):
    radii=[1.,1.2];v,m,ne,nf=geometry(radii,0,depth);n=len(v)
    D=np.tile([1.,0.,2.],(n,1));nu=np.tile([.5,.3,.2],(n,1));g=np.tile([.2,.3,-.1],(n,1));axis=np.tile([0.,0.,1.],(n,1))
    a=construct(radii,0,np.arange(n),v,D,nu,g,axis,nested_depth=depth,sparse_operator=True)
    p=structural_stage_atlas(a,m);N=a['generator'].shape[0]
    assert (n,N)==((576,7140) if depth else (24,314))
    assert close(a['exchange'],-a['exchange'].T,rtol=0,atol=0)
    x=np.zeros(N);x[0]=1.;f=np.zeros_like(x);f[0]=.1
    u,ra=timed_step(x,a['generator'],f,.001,m,{'collision':a['loss']},atlas_pairs=p)
    assert abs((u@u-x@x)/2-ra['work_J']+ra['loss_J'])<1e-10
    if not depth:
        b=construct(radii,0,np.arange(n),v,D,nu,g,axis)
        assert close(b['generator'],a['generator'],rtol=0,atol=0)
        assert p==structural_stage_atlas(b,m)
        w,rb=timed_step(x,b['generator'],f,.001,m,{'collision':b['loss']},atlas_pairs=p)
        assert np.array_equal(u,w);ra.pop('sparse_operator');rb.pop('sparse_operator');assert ra==rb
    # Exact same coefficient/geometry cache replay, not a new approximation.
    b=construct(radii,0,np.arange(n),v,D,nu,g,axis,nested_depth=depth,sparse_operator=True)
    assert close(a['generator'],b['generator'],rtol=0,atol=0)
    print(dict(status='NATIVE_ASSEMBLY_PASS',depth=depth,cells=n,coordinates=N,
        operator_nonzeros=a['generator'].nnz,structural_pairs=len(p),stages=len(ra['events']),
        dense_sparse_parity=not bool(depth),cache_hits=_prepared_static_geometry.cache_info().hits,
        energy_residual=float(abs((u@u-x@x)/2-ra['work_J']+ra['loss_J'])),physical_admission=False))
if __name__=='__main__':
    import sys
    run(int('--nested' in sys.argv))
