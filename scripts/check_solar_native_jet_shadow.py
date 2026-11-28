"""Actual 24-cell coefficient, multi-step shadow, support-boundary acceptance."""
import numpy as np
from scipy.sparse import eye
from solar_synthetic_fixture import fixture
from solar_spherical_reverse_jvp import campaign_jvp
from solar_spherical_cycle import cycle

def run():
    m,c,h,l=fixture();c=dict(c,common_stage_atlas=True,retain_jet_history=True)
    a=campaign_jvp(m,c,h,l,quadratic_amplitude_path=True,quadratic_second_order=True)
    b=campaign_jvp(m,dict(c,sparse_operator=True),h,l,quadratic_amplitude_path=True,quadratic_second_order=True)
    assert all(np.array_equal(x,y) for k in ('endpoint','endpoint_jvp','endpoint_coefficient2') for x,y in zip(a[k],b[k]))
    assert a['net_coefficient2_J']==b['net_coefficient2_J']
    ref=np.array([[r[k] for k in ('field','first','second')] for r in a['indexed_jet_history']])
    ref[0,:,0]+=[.00001,.00002,.00003]
    s=campaign_jvp(m,c,h,l,quadratic_amplitude_path=True,quadratic_second_order=True,shadow=dict(
        prolongation=eye(ref.shape[2]),endpoints=ref,useful_coefficients_J=[r['useful_coefficients_J'] for r in a['indexed_jet_history']]))
    traces=s['signed_jet_evolution_residual_trace']
    assert len(traces)==5 and max(traces[1]['observed_propagation_error'])>0
    assert all(np.all(np.asarray(r['endpoint_error'])<=np.asarray(r['error_bound_candidate'])+1e-15) for r in traces)
    rows,neutral,D,g,axis=m;m=(rows,neutral,np.zeros_like(D),np.ones_like(g)*.2,axis)
    n=len(rows);c=dict(c,heating_W=np.zeros((2,n)).tolist())
    q=dict(c['kinetics'],recombination_m3_s=[0.,0.],ionization_s_inv=[0.,0.],heater_ionization_per_J=[.01,.02])
    birth=np.zeros((n,3,3));birth[0,:,0]=1e5;q['birth_velocity_m_s']=birth.tolist();c['kinetics']=q
    h=np.zeros((2,n));h[0,0]=.2;l=np.zeros_like(l);l[0]=.01
    j=campaign_jvp(m,c,h,l,quadratic_amplitude_path=True,quadratic_second_order=True)
    base=cycle(m,c);x=j['endpoint'][0];x1=j['endpoint_jvp'][0];x2=j['endpoint_coefficient2'][0]
    assert np.allclose(np.asarray(base['history'][-1])[:len(x)],x,rtol=1e-12,atol=1e-14)
    errors=[]
    for eps in (.01,.001):
        out=cycle(m,dict(c,heating_W=(eps*eps*h).tolist(),load_rate_s_inv=(np.array(c['load_rate_s_inv'])+eps*eps*l).tolist()))
        fd=(np.array(out['history'][-1])[:len(x)]-x-eps*x1)/(eps*eps)
        err=np.linalg.norm(fd-x2)/max(np.linalg.norm(x2),1e-12)
        w=(out['campaign_net_J']-base['campaign_net_J']-eps*j['dcampaign_net_J'])/(eps*eps)
        errw=abs(w-j['net_coefficient2_J'])/max(abs(j['net_coefficient2_J']),1e-12)
        errors.append([eps,float(err),float(errw)])
    assert errors[-1][1]<1e-4 and errors[-1][1]<errors[0][1]/5 and errors[-1][2]<1e-8
    print(dict(status='NATIVE_JET_SHADOW_PASS',dense_sparse_exact=True,steps=5,
        positive_net2=a['net_coefficient2_J'],shadow_state_bounds=s['jet_endpoint_error_bound_candidate'],
        shadow_work_bounds_J=s['jet_receiver_work_error_bound_candidate_J'],zero_support_errors=errors,physical_admission=False))
if __name__=='__main__':run()
