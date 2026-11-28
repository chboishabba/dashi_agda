"""Original 24-cell shell, exact signed nested mesh, three coefficient histories."""
import numpy as np
from solar_spherical_whitney import shell_mesh,whitney
from solar_nested_cochain_refinement import nested_cochains,metric_pullback,endpoint_time_complement,maxwell_galerkin_weld,material_cell_maps

def run():
    xyz,s,m,_=shell_mesh([1.,1.2],0)
    b=nested_cochains(xyz,s);f=b['simplices']
    assert len(s[3])==24 and len(f[3])==576
    assert b['exact_cochain_squares']==6 and b['exact_reopen_degrees']==4
    E,B,V=whitney(xyz,s,m)
    Ef,Bf,Vf=whitney(b['xyz'],f,[{t:i for i,t in enumerate(row)} for row in f])
    assert np.isclose(V,Vf,rtol=1e-12,atol=0)
    pull=metric_pullback(b,(E,B),(Ef,Bf))
    assert all(r['consistent_relative_defect']<1e-12 for r in pull)
    # The diagonal metric is a distinct candidate, not the consistent metric.
    assert all(r['diagonal_relative_defect']>1e-3 for r in pull)
    gal=maxwell_galerkin_weld(b,(E,B),(Ef,Bf))
    assert gal['isometry_error']<1e-11 and gal['projected_relative_defect']<1e-11
    assert gal['magnetic_relative_defect']<1e-11 and gal['full_relative_defect']>1e-3
    material=material_cell_maps(b,xyz,s)
    assert np.all(np.bincount(material['owner'])==24)
    rng=np.random.default_rng(369);worst=0.
    for k in range(4):
        fine=rng.normal(size=(6,3,len(f[k]))); coarse=rng.normal(size=(3,3,len(s[k])))
        out=endpoint_time_complement(b,k,fine,coarse)
        worst=max(worst,out['reconstruction_error'])
        assert not np.any(out['square_residual'])
        assert np.any(out['signed_residual']<0) and np.any(out['signed_residual']>0)
    print(dict(status='NESTED_COCHAIN_PASS',coarse=[len(row) for row in s],
        fine=[len(row) for row in f],exact_squares=6,reopen_degrees=4,
        consistent_defect=[r['consistent_relative_defect'] for r in pull],
        diagonal_defect=[r['diagonal_relative_defect'] for r in pull],
        reconstruction_error=worst,galerkin_relative_defect=gal['projected_relative_defect'],
        full_operator_defect=gal['full_relative_defect'],magnetic_lift_defect=gal['magnetic_relative_defect'],
        material_volume_error=material['relative_volume_error'],physical_admission=False))
if __name__=='__main__':run()
