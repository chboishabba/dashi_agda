#!/usr/bin/env python3
"""J22 original J18 nine-state source consumer: numerical saltation and shooting.

Synthetic externally prescribed wave, not a measured Filsinger device, Earth
source, or proof of an exactly existing orbit. No global/interval certification.
Reuses the native J18 integrator for independent high-accuracy work replay and
requires original J18/J19/J20/J21 source blobs; does NOT change native owners.
"""
import json
import math
import numpy as np
from scipy.integrate import solve_ivp
import check_smith_filsinger_j18_hf_spark_tank_20261123 as hf
import check_smith_filsinger_j19_zero_freewheel_inverse_20261123 as j19
import check_smith_filsinger_j20_perfect_capture_reactive_return_20261123 as j20
import check_smith_filsinger_j21_source_only_throughput_20261123 as j21

SHA = dict(J18='f4270a475f010874056cfe3cdeff5ee8e43c44eb',
           J19='cc5cec2d4f881b38b4c01ef79dd93f36e9ef1439',
           J20='ed09b82287ec1ca0318b4f8e9d355f614d00d894',
           J21='b4c865f465f1a4a2e8dd40820eb02a6456454d67')
P = hf.native.BASE | hf.DEFAULT | j19.P | j20.COMMON | j21.OPT
PHASE = .3
T = hf.native.T
LI = np.linalg.inv(np.array([[P['L1'],P['M']],[P['M'],P['L2']]]))
AI = np.linalg.inv(np.array([[P['C']+P['Cu'],-P['C']],[-P['C'],P['C']+P['Cv']]]))

def rhs(t,z,on):
    i,j,u,v,b,q,r,ih,x = z
    drv=P.get('drive_amp',2.)*math.sin(t)
    a=P['omega']*t+PHASE
    sr=P['source_amp']*math.cos(a)
    si=P['wave_handedness']*P['source_amp']*math.sin(a)
    ju=max((u-b-P['Vd'])/P['Rd'],0.)
    jv=max((v-b-P['Vd'])/P['Rd'],0.)
    ij=LI@np.array([drv-P['R1']*i,u-v-P['R2']*j])
    uv=AI@np.array([-j-ju+P['k']*q+P['kh']*ih,j-jv])
    bd=(ju+jv-P['Gbleed']*b-on*ih)/P['Cb']
    g=P['gamma_rad']+P['gamma_internal']
    rad=math.sqrt(2*P['gamma_rad'])
    dq=P['omega']*r-g*q-P['k']*u/2+rad*sr
    dr=-P['omega']*q-g*r+rad*si
    di=(on*b-x-(P['Rcoil']+on*P['Rgap'])*ih-P['kh']*u)/P['Lh']
    dx=(ih-P['Gload']*x)/(P['Ch']*(1+3*P['alpha']*x*x))
    return np.r_[ij,uv,bd,dq,dr,di,dx]

def jacobian(z,on):
    i,j,u,v,b,q,r,ih,x=z
    au=float(u-b-P['Vd']>0)/P['Rd']
    av=float(v-b-P['Vd']>0)/P['Rd']
    J=np.zeros((9,9))
    d=np.zeros((2,9))
    d[0,0]=-P['R1'];d[1,1]=-P['R2'];d[1,2]=1.;d[1,3]=-1.
    J[:2,:]=LI@d
    d=np.zeros((2,9))
    d[0,1]=-1.;d[0,2]=-au;d[0,4]=au;d[0,5]=P['k'];d[0,7]=P['kh']
    d[1,1]=1.;d[1,3]=-av;d[1,4]=av
    J[2:4,:]=AI@d
    J[4,2]=au/P['Cb'];J[4,3]=av/P['Cb']
    J[4,4]=(-au-av-P['Gbleed'])/P['Cb'];J[4,7]=-on/P['Cb']
    g=P['gamma_rad']+P['gamma_internal']
    J[5,2]=-P['k']/2;J[5,5]=-g;J[5,6]=P['omega']
    J[6,5]=-P['omega'];J[6,6]=-g
    J[7,2]=-P['kh']/P['Lh'];J[7,4]=on/P['Lh']
    J[7,7]=-(P['Rcoil']+on*P['Rgap'])/P['Lh'];J[7,8]=-1/P['Lh']
    den=P['Ch']*(1+3*P['alpha']*x*x)
    J[8,7]=1/den
    J[8,8]=-P['Gload']/den-(ih-P['Gload']*x)*6*P['alpha']*x/(P['Ch']*(1+3*P['alpha']*x*x)**2)
    return J

def switched_tangent(x0,rtol=3e-10,atol=3e-12,max_step=.035):
    y=np.r_[np.asarray(x0),np.eye(9).ravel()]
    on=True; t=0.; events=[]
    for _ in range(400):
        if t>=T-1e-11: break
        def extended(t,y):
            z=y[:9];Z=y[9:].reshape(9,9)
            return np.r_[rhs(t,z,on),(jacobian(z,on)@Z).ravel()]
        def event(t,y): return y[4]-(P['Voff'] if on else P['Von'])
        event.terminal=True;event.direction=-1 if on else 1
        sol=solve_ivp(extended,(t,T),y,rtol=rtol,atol=atol,
                      max_step=max_step,events=event)
        assert sol.success,sol.message
        t=float(sol.t[-1]);y=sol.y[:,-1]
        if not len(sol.t_events[0]): break
        z=y[:9]
        fm=rhs(t,z,on);fp=rhs(t,z,not on)
        slope=fm[4]
        assert (1 if not on else -1)*slope>0
        # Identity state reset, finite switch-time correction.
        salt=np.eye(9);salt[:,4]+=(fp-fm)/slope
        y[9:]=(salt@y[9:].reshape(9,9)).ravel()
        events.append(dict(time=t, label='off' if on else 'on',
                           signed_slope=(1 if not on else -1)*slope))
        on=not on
    else: raise RuntimeError('event overflow')
    M=y[9:].reshape(9,9)
    return dict(endpoint=y[:9],end_on=on,events=events,M=M,
                spectral_radius=float(np.max(np.abs(np.linalg.eigvals(M)))),
                singular_values=np.linalg.svd(np.eye(9)-M,compute_uv=False))

def native_seed():
    x=np.zeros(9);on=False
    for n in range(13):
        y,new_on,r=hf.advance(P,True,PHASE,state=x,active=on,t0=n*T,
                            rtol=3e-8,atol=5e-10,max_step=.055)
        if np.max(np.abs(y-x))<2e-5 and new_on==on:
            assert len(r['event_log'])==22
            assert on and new_on
            return y
        x=y;on=new_on
    raise AssertionError('no native 22-event near-periodic seed')

def run():
    assert all(j20.blob(module.__file__)==SHA[key] for key,module in
        [('J18',hf),('J19',j19),('J20',j20),('J21',j21)])
    assert P['drive_amp']==0 and P['wave_handedness']==-1 and P['off_return']=='capacitive'
    assert P['Rcoil']>0 and P['Rgap']>0 and P['Gload']>0
    x=native_seed()
    history=[]
    for iteration in range(4):
        sol=switched_tangent(x,rtol=2e-11,atol=2e-13,max_step=.028)
        residual=float(np.max(np.abs(sol['endpoint']-x)))
        history.append(residual)
        assert len(sol['events'])==22 and sol['end_on']
        assert min(q['signed_slope'] for q in sol['events'])>.08
        assert sol['spectral_radius']<.4
        assert min(sol['singular_values'])>.7
        if residual<1e-10: break
        x=x+np.linalg.solve(np.eye(9)-sol['M'],sol['endpoint']-x)
    else:raise AssertionError('shooting Newton failed')
    assert len(history)>=2
    a=switched_tangent(x,rtol=3e-8,atol=3e-10,max_step=.035)
    b=switched_tangent(x,rtol=3e-10,atol=3e-12,max_step=.035)
    rel=float(np.linalg.norm(a['M']-b['M'])/np.linalg.norm(b['M']))
    assert rel<1e-3 and len(a['events'])==len(b['events'])==22
    y,on,work=hf.advance(P,True,PHASE,state=x,active=True,t0=0.,
                         rtol=3e-11,atol=3e-13,max_step=.028)
    labels=[label for _,label in work['event_log']]
    assert on and labels==[q['label'] for q in b['events']]
    assert len(labels)==22
    closure=float(np.max(np.abs(y-x)))
    assert closure<1e-7 and abs(work['residual'])<1e-7
    assert abs(work['storage_delta'])<1e-7 and work['driver']==0
    eta=work['hf_load']/work['incident']
    cap=(work['incident']-work['outgoing'])/work['incident']
    assert abs(eta-.5146193248)<1e-5
    assert abs(cap-.6567344553)<1e-5
    return dict(status='J22_NATIVE_SOURCE_SALTATION_NUMERICAL_PASS_IF_EXECUTED',
       upstream_blobs=SHA,shooting_residual_history=history,
       native_cycle_closure=closure,native_energy_residual=work['residual'],
       native_storage_delta=work['storage_delta'],
       source_only_load_fraction=eta,wave_capture_fraction=cap,
       min_signed_switch_slope=min(q['signed_slope'] for q in b['events']),
       event_count=len(labels),event_times=[t for t,_ in work['event_log']],
       spectral_radius=b['spectral_radius'],
       smallest_singular_IminusM=float(min(b['singular_values'])),
       condition_IminusM=float(max(b['singular_values'])/min(b['singular_values'])),
       rel_tangent_tolerance_difference=rel,
       numerical_noninterval_not_physical_evidence=True,
       exact_zero_loss_hardware_claim=False,
       github_actions_or_ci_run=False,agda_kernel_run=False)

if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
