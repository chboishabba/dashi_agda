"""Original spherical two-jet path acceptance, separate from local algebra."""
import numpy as np
from check_solar_spherical_reverse_integration import fixture
from solar_spherical_cycle import cycle,geometry
from solar_spherical_reverse_jvp import campaign_jvp


def run():
    mat,cfg,_,_=fixture()
    rows,neutral,D,gyro,axis=mat
    _,_,ne,nf=geometry(cfg['radii_m'],cfg['angular_level'])
    n=len(rows);assert n==24
    mat=(rows,neutral,np.zeros_like(D),np.ones_like(gyro)*.2,axis)
    cfg=dict(cfg,common_stage_atlas=True,source_version='synthetic-twojet-v1',
        temporal_depth=1,heating_W=np.zeros((2,n)).tolist(),retain_jet_history=True)
    kin=dict(cfg['kinetics'],recombination_m3_s=[0.,0.],
        ionization_s_inv=[0.,0.],heater_ionization_per_J=[.01,.02])
    birth=np.zeros((n,3,3));birth[0,:,0]=1e5
    kin['birth_velocity_m_s']=birth.tolist();cfg['kinetics']=kin
    dh=np.zeros((2,n));dh[0,0]=.2;dl=np.zeros(ne);dl[0]=.01
    j=campaign_jvp(mat,cfg,dh,dl,quadratic_amplitude_path=True,quadratic_second_order=True)
    base=cycle(mat,cfg);x=j['endpoint'][0];x1=j['endpoint_jvp'][0];x2=j['endpoint_coefficient2'][0]
    N=len(x); assert np.allclose(np.asarray(base['history'][-1])[:N],x,rtol=1e-10,atol=1e-14)
    assert len(j['indexed_jet_history'])==len(j['coefficient2_energy_ledger'])
    assert j['campaign_discrete_reach_checked']
    reconstructed=np.zeros((n,3))
    for item in j['indexed_event_residuals']: reconstructed[item['cell']]+=item['signed_coefficient2_residual']
    assert np.allclose(reconstructed,0.,atol=1e-12) # these births start at order s, not s^2
    errors=[]
    for s in (.01,.001):
        out=cycle(mat,dict(cfg,heating_W=(s*s*dh).tolist(),
            load_rate_s_inv=(np.asarray(cfg['load_rate_s_inv'])+s*s*dl).tolist()))
        final=np.asarray(out['history'][-1])[:N]
        fd=(final-x-s*x1)/(s*s)
        state_err=np.linalg.norm(fd-x2)/max(np.linalg.norm(x2),1e-12)
        work=(out['campaign_net_J']-base['campaign_net_J']-s*j['dcampaign_net_J'])/(s*s)
        net_err=abs(work-j['net_coefficient2_J'])/max(abs(j['net_coefficient2_J']),1e-12)
        assert state_err<.05 and net_err<.05,(s,state_err,net_err)
        errors.append([s,float(state_err),float(net_err)])
    print(dict(status='NATIVE_SPHERICAL_TWO_JET_PASS',errors=errors,
        net2_J=j['net_coefficient2_J'],physical_admission=False))


if __name__=='__main__':run()
