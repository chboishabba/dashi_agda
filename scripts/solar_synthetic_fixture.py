"""Shared original synthetic 24-cell spherical acceptance fixture."""
import numpy as np
from solar_spherical_geometry import geometry
from solar_population_event import MASS,CHARGE

def fixture():
    radii=[1.,1.2];level=0
    vol,mesh,ne,nf=geometry(radii,level);n=len(vol)
    pop=np.tile([1.e8,6.e7,4.e7],(n,1))
    D=pop*CHARGE**2/MASS
    rows=[dict(te=1000.,ti=1000.) for _ in range(n)]
    neutral=np.zeros((n,11)); neutral[:,1:4]=[1e15,2e15,1.5e15]
    neutral[:,10]=1000.
    material=(rows,neutral,D,np.zeros((n,3)),np.tile([0.,0.,1.],(n,1)))
    q=dict(initial_neutral_m3=np.full((n,2),5e7),
        recombination_m3_s=[1e-11,1e-11],
        ionization_s_inv=[.01,.02],
        heater_ionization_per_J=[.01,.02],
        activation_temperature_K=[900.,900.],
        formation_J_per_particle=[0.,0.,0.],
        birth_velocity_m_s=np.zeros((n,3,3)).tolist(),
        chemical_input_efficiency=1.,chemical_recovery_efficiency=0.)
    cfg=dict(radii_m=radii,angular_level=level,
        row_keys=[f'synthetic:{i}' for i in range(n)],
        incident_sqrt_W=[.2,-.1],
        heating_W=np.full((2,n),.005).tolist(),
        load_rate_s_inv=np.r_[.04,np.zeros(ne-1)].tolist(),
        period_s=2e-4,max_cycles=2,source_edge=0,
        source_coupling_sqrt_inv_s=.2,
        kinetics=q,heat_capacity_J_K=np.ones(n).tolist(),
        cooling_W_K=(np.ones(n)*.2).tolist(),
        heater_efficiency=.8,auxiliary_J=0.,
        restoration_steps=1,return_rtol=1e-12,
        # Tight return tolerances: distinguish a small residual from genuine
        # original restoration; no artificial 1e-3 absolute field allowance.
        return_atol=[1e-12,1e-8,1e-8,1e-12],
        fixed_horizon=True,retain_history=True)
    dheat=np.zeros((2,n));dheat[:,0]=[.2,-.1]
    dload=np.zeros(ne);dload[0]=.08
    return material,cfg,dheat,dload
