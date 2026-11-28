"""Positive-population native spherical JVP versus same-solver perturbations.

Run locally: python scripts/check_solar_spherical_reverse_integration.py
No external original-data inference. A failure is an actionable acceptance failure,
not a license to relax a restoration or energy ledger.
"""
import json
import numpy as np
from solar_spherical_cycle import cycle,geometry
from solar_spherical_reverse_jvp import campaign_jvp
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

def run(common_atlas=False):
    material,cfg,dheat,dload=fixture()
    cfg['common_stage_atlas']=bool(common_atlas)
    vol,mesh,ne,nf=geometry(cfg['radii_m'],cfg['angular_level']);n=len(vol)
    base=campaign_jvp(material,cfg,dheat,dload)
    zero=cycle(material,cfg)
    assert abs(zero['campaign_net_J']-base['campaign_net_J']) < 1e-7*max(1,abs(zero['campaign_net_J']))
    tests=[]
    initial=(np.zeros_like(base['endpoint'][0]),np.asarray(material[2])*MASS/CHARGE**2,
             np.asarray(cfg['kinetics']['initial_neutral_m3']),np.zeros(n))
    def distance_squared(state):
        return sum(float(np.sum((v-u)**2)) for v,u in zip(state,initial))
    assert np.isclose(distance_squared(base['endpoint']),base['restoration_squared'],rtol=1e-9,atol=1e-7)
    for eps in (1e-3,1e-4):
        vals=[]
        for sign in (+1,-1):
            cc=dict(cfg)
            cc['heating_W']=(np.asarray(cfg['heating_W'])+sign*eps*dheat).tolist()
            cc['load_rate_s_inv']=(np.asarray(cfg['load_rate_s_inv'])+sign*eps*dload).tolist()
            assert np.min(cc['heating_W'])>=0 and np.min(cc['load_rate_s_inv'])>=0
            vals.append(cycle(material,cc))
        fd=(vals[0]['campaign_net_J']-vals[1]['campaign_net_J'])/(2*eps)
        error=abs(fd-base['dcampaign_net_J'])
        states=[]
        for out in vals:
            z=np.asarray(out['history'][-1],float);k=ne+nf+9*n
            states.append((z[:k],z[k:k+3*n].reshape(n,3),z[k+3*n:k+5*n].reshape(n,2),z[k+5*n:]))
        terminal_errors=[]
        fd_restoration=(distance_squared(states[0])-distance_squared(states[1]))/(2*eps)
        restoration_error=abs(fd_restoration-base['drestoration_squared'])/max(1.,abs(fd_restoration),abs(base['drestoration_squared']))
        assert restoration_error<1e-4,(eps,restoration_error)
        for k in range(4):
            d=(states[0][k]-states[1][k])/(2*eps)
            analytic=np.asarray(base['endpoint_jvp'][k])
            err=float(np.linalg.norm(d-analytic)/max(1.,np.linalg.norm(analytic)))
            terminal_errors.append(err)
            assert err < 1e-4,(k,eps,err)
        tests.append(dict(epsilon=eps,work_derivative_error_J=error,
                          terminal_relative_jvp_errors=terminal_errors,
                          restoration_squared_jvp_relative_error=restoration_error))
        assert error < 1e-5*max(1.,abs(fd))
    return dict(status='NATIVE_SYNTHETIC_SPHERICAL_JVP_PASS',
                common_stage_atlas=bool(common_atlas),
                n_cells=len(cfg['row_keys']),work_jvp=base['dcampaign_net_J'],
                original_return_squared=base['restoration_squared'],
                derivative_tests=tests,full_original_restored=bool(zero['full_original_restored']),
                strict_campaign_net_J=zero['strict_campaign_net_J'],
                positive_physical_endpoint_claim=False)
if __name__=='__main__':
    import sys
    print(json.dumps(run('--common-atlas' in sys.argv),indent=2))
