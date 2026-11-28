"""Native static geometry cache parity against uncached Whitney/Hodge construction."""
import numpy as np
from solar_spherical_whitney import shell_mesh
from solar_spherical_material_weld import construct,_prepared_static_geometry

def run():
    radii=[1.,1.2];xyz,s,m,d=shell_mesh(radii,0)
    owners=np.zeros(len(s[3]),int)
    volume=sum(abs(np.linalg.det((xyz[list(t)][1:]-xyz[t[0]]).T))/6 for t in s[3])
    args=(tuple(radii),0,tuple(owners),tuple([volume]))
    uncached=_prepared_static_geometry.__wrapped__(*args)
    _prepared_static_geometry.cache_clear()
    first=_prepared_static_geometry(*args)
    second=_prepared_static_geometry(*args)
    assert len(first)==len(uncached)
    assert all(np.array_equal(a,b) for a,b in zip(first,uncached))
    assert all(a is b for a,b in zip(first,second))
    assert _prepared_static_geometry.cache_info().hits>=1
    d1=np.array([[1.,2.,3.]])
    d2=np.array([[1.5,2.5,3.5]])
    nu=np.array([[.3,.4,.5]])
    gyro=np.zeros((1,3));axis=np.array([[0.,0.,1.]])
    a=construct(radii,0,owners,[volume],d1,nu,gyro,axis)
    b=construct(radii,0,owners,[volume],d2,nu,gyro,axis)
    assert np.array_equal(a['consistent_masses'][0],b['consistent_masses'][0])
    assert np.array_equal(a['consistent_masses'][1],b['consistent_masses'][1])
    assert np.array_equal(a['material_map'],b['material_map'])
    assert not np.array_equal(a['generator'],b['generator'])
    assert np.array_equal(a['generator']+a['generator'].T,-2*a['loss'])
    return dict(status='PASS',cached_static_reused=True,
                bitwise_uncached_parity=True,material_dynamics_not_cached=True)
if __name__=='__main__':
    print(run())
