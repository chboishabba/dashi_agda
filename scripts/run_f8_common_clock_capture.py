"""Original mode3 common-clock independent-axis and stage-time window capture.
Original producer unchanged; window history fails closed on missing samples.
"""
import argparse,hashlib,json,math,sys
from pathlib import Path
import numpy as np
import ksw668_f8_tt_multipole as original
from run_f8_p0_native_receiver_state_capture import main as capture_main,atomic_npz
from check_f8_parity_capture_tail import capture,radial_rows,geometry_rows
from run_f8_safe_source_capture import configuration as safe_config
from scipy.integrate import quad

T0=original.F(1);Tend=original.F(12);span=Tend-T0;nt=7225;dt=span/nt
bulk=math.sqrt(span**2-(1-1/12)**2)

def configuration(label,axis):
    c=safe_config(label);c['dt']=span/(nt-.25)
    if axis=='normal':
        assert label[0]=='A';c['dy']=.009
    else:assert axis=='common'
    assert math.ceil(span/c['dt'])==nt and c['dt']*(7/c['dr']+10/c['dy']+400)<1
    return c

def weight(T):
    x=(T-Tend+.15)/.1
    return math.exp(1-1/(1-x*x)) if abs(x)<1 else 0.

required=[i for i in range(nt+1) if weight(T0+i*dt)>0]

def observe(U,P,M,W,Pt,Mt,dr,h,b,v,r,eps):
    ids,w,L,X=radial_rows(r,dr,eps,U.shape[-1]);t=1/b;a,c=1+v,1-v
    o=lambda x,weights=w:np.sum(x[:,ids]*weights,axis=1)
    A=o(W[:,0]);B=o((a*Pt[:,0]+c*Mt[:,0])/2+t**3/(1+t*t)**2*(P[:,0]-M[:,0])/2)
    lap=o(U[:,0],L);ax=o(U[:,0],X)
    d=(-3*U[:,0]+4*U[:,1]-U[:,2])/(2*h);e=(-3*W[:,0]+4*W[:,1]-W[:,2])/(2*h);y=(U[:,2]-2*U[:,1]+U[:,0])/h**2
    de=(U[:,2]-U[:,0])/(2*h);ee=(W[:,2]-W[:,0])/(2*h);ye=(U[:,4]-2*U[:,2]+U[:,0])/(4*h*h)
    rows=geometry_rows(t)
    return np.stack([rows@np.stack([A,B,o(d),o(e),o(y),lap,ax]),rows@np.stack([A,B,o(de),o(ee),o(ye),lap,ax])])

def main():
    p=argparse.ArgumentParser();p.add_argument('label',choices=('A0','A1','C0','C1'));p.add_argument('--axis',choices=('common','normal'),default='common');p.add_argument('--work',type=Path,required=True);p.add_argument('--budget',type=float,default=12.);a=p.parse_args()
    assert 0<a.budget<=90
    c=configuration(a.label,a.axis);a.work.mkdir(parents=True,exist_ok=True)
    wp=a.work/(a.label+'.window.npz');ck=a.work/(a.label+'.npz');prod=a.work/(a.label+'.json');identity=json.dumps(c,sort_keys=True);seen={}
    if wp.exists():
        with np.load(wp,allow_pickle=False) as z:
            assert z['identity'].item()==identity;seen={int(i):x for i,x in zip(z['indices'],z['observations'])}
    if ck.exists():
        with np.load(ck,allow_pickle=False) as z:cursor=int(z['cursor'].item())
        if any(i not in seen for i in required if i<cursor):raise ValueError('missing window history before checkpoint cursor')
    stage=original.stage
    def observed_stage(U,P,M,outU,outP,outM,dr,dy,b,v,amp,src,cp,cm,normal_order):
        stage(U,P,M,outU,outP,outM,dr,dy,b,v,amp,src,cp,cm,normal_order)
        f=sys._getframe(2);l=f.f_locals;i=l.get('it',-1)
        if f.f_code.co_name=='propagate' and i in required and l.get('U') is U and l.get('P') is P and l.get('M') is M:
            assert amp==0. and normal_order==3 and i not in seen
            seen[i]=np.stack([observe(U,P,M,outU,outP,outM,dr,dy,b,v,r,c['eps']) for r in (bulk-.012,bulk+.1)])
    def driver():
        try:result=original.propagate(**c,checkpoint=ck,budget=a.budget,checkpoint_every=16)
        except InterruptedError as e:print(e,flush=True);return 75
        assert result['steps']==nt and result['step_time']==dt
        tmp=prod.with_suffix('.tmp');tmp.write_text(json.dumps(result,indent=2)+'\n');tmp.replace(prod);return 0
    original.stage=observed_stage;argv=sys.argv[:]
    try:
        sys.argv=[argv[0],a.label,'--work',str(a.work),'--budget',str(a.budget)]
        status=capture_main(driver_main=driver,driver_name='run_f8_common_clock_capture.'+a.axis,default_work=str(a.work))
    finally:
        sys.argv=argv;original.stage=stage
        if seen:atomic_npz(wp,identity=identity,indices=np.array(sorted(seen)),observations=np.stack([seen[i] for i in sorted(seen)]))
    if status:return status
    assert sorted(seen)==required
    packet=capture(ck,a.work/(a.label+'.receiver-state.npz'),prod)
    (a.work/(a.label+'.packets.json')).write_text(json.dumps(packet,indent=2)+'\n')
    norm=quad(lambda x:math.exp(1-1/(1-x*x)),-1,1,epsabs=1e-13)[0]*.1
    weights=np.array([weight(T0+i*dt)*dt/norm for i in required]);obs=np.stack([seen[i] for i in required]);window=np.einsum('i,ipkrm->pkrm',weights,obs)
    signed=np.einsum('i,ipm->pm',weights,obs[:,:,0,2,:]-obs[:,:,1,2,:]);absolute=np.einsum('i,ipm->pm',weights,abs(obs[:,:,0,2,:]-obs[:,:,1,2,:]))
    assert np.allclose(signed,window[:,0,2,:]-window[:,1,2,:],rtol=1e-10,atol=1e-17)
    sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
    receipt=dict(label=a.label,axis=a.axis,config=c,actual_dt=dt,window_samples=len(required),window_weight_sum=float(weights.sum()),window_rows=['E4','legacy4','direct','SMS','F','R'],window_packets=['raw_stage_time','parity_stage_time'],places=['near','far'],window_signed=window.tolist(),window_raw_minus_parity_direct=signed.tolist(),window_absolute_raw_minus_parity_direct=absolute.tolist(),terminal=packet['receivers'],sha256={k:sha(a.work/(a.label+s)) for k,s in [('checkpoint','.npz'),('sidecar','.receiver-state.npz'),('production','.json'),('packets','.packets.json'),('window','.window.npz')]},scope='original safe common clock, stage-time fixed-window quadrature; no continuum or interval propagation certificate')
    (a.work/(a.label+'.axis.json')).write_text(json.dumps(receipt,indent=2)+'\n');print(a.work/(a.label+'.axis.json'),flush=True);return 0

if __name__=='__main__':raise SystemExit(main())
