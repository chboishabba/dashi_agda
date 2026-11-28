"""Actual 24-cell forward/reverse path, quadratic birth at zero density.
Synthetic inputs, no physical source admission. Run in local 90s lane.
"""
import numpy as np
from check_solar_spherical_reverse_integration import fixture
from solar_spherical_cycle import cycle,geometry
from solar_spherical_reverse_jvp import campaign_jvp
from solar_physical_causal import MASS,CHARGE


def run():
    mat,cfg,_,_=fixture()
    rows,neutral,D,gyro,axis=mat
    _,_,ne,nf=geometry(cfg['radii_m'],cfg['angular_level'])
    n=len(rows); assert n==24
    mat=(rows,neutral,np.zeros_like(D),np.ones_like(gyro)*.2,axis)
    cfg=dict(cfg,common_stage_atlas=True,source_version='synthetic-quadratic-v1',
             temporal_depth=1,heating_W=np.zeros((2,n)).tolist())
    kin=dict(cfg['kinetics'],recombination_m3_s=[0.,0.],
             ionization_s_inv=[0.,0.],heater_ionization_per_J=[.01,.02])
    b=np.zeros((n,3,3));b[0,:,0]=1e5
    kin['birth_velocity_m_s']=b.tolist();cfg['kinetics']=kin
    direction=np.zeros((2,n));direction[0,0]=.2
    load_dir=np.zeros(ne)
    base=cycle(mat,cfg)
    tangent=campaign_jvp(mat,cfg,direction,load_dir,quadratic_amplitude_path=True)
    x,poolpop,reservoir,theta=tangent['endpoint']
    dx=tangent['endpoint_jvp'][0]
    pop_u,pool_u,theta_u=tangent['population_pool_temperature_u_jvp']
    assert np.any(pop_u[0]>0) and np.all(pop_u[1:]==0)
    assert np.all(poolpop==0) and np.all(tangent['endpoint_jvp'][1]==0)
    assert np.linalg.norm(dx[ne+nf:])>0
    last=np.asarray(base['history'][-1]); N=len(x)
    assert np.allclose(last[:N],x,rtol=1e-10,atol=1e-14)
    assert abs(base['campaign_net_J']-tangent['campaign_net_J'])<1e-12
    # Reconstruct the amplitude endpoint and its signed directional residual.
    residual=np.zeros((n,3));dresidual=np.zeros_like(residual)
    for item in tangent['indexed_event_residuals']:
        i=item['cell'];residual[i]+=item['signed_amplitude_residual']
        dresidual[i]+=item['signed_tangent_residual']
        assert item['index']['history']==cfg['row_keys'][i]
        assert item['index']['iteration'] is None
    assert np.allclose(residual,np.sqrt(poolpop))
    assert np.allclose(dresidual,np.sqrt(pop_u))
    errors=[]
    for s in (.01,.001):
        pert=dict(cfg,heating_W=(s*s*direction).tolist())
        out=cycle(mat,pert); final=np.asarray(out['history'][-1])
        fd=(final[:N]-last[:N])/s
        err=np.linalg.norm(fd[ne+nf:]-dx[ne+nf:])/np.linalg.norm(dx[ne+nf:])
        actual_pop=final[N:N+3*n].reshape(n,3)
        perr=np.linalg.norm(actual_pop/(s*s)-pop_u)/np.linalg.norm(pop_u)
        paid=(out['campaign_ledger']['paid_J']-base['campaign_ledger']['paid_J'])/(s*s)
        cerr=abs(paid-tangent['paid_u_jvp'])/max(abs(tangent['paid_u_jvp']),1e-30)
        assert max(err,perr,cerr)<.02,(s,err,perr,cerr)
        errors.append([float(s),float(err),float(perr),float(cerr)])
    print(dict(status='SPHERICAL_QUADRATIC_PATH_PASS',cells=n,errors=errors,
               physical_admission=False))


if __name__=='__main__': run()
