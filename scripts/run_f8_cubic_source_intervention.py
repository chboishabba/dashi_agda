"""Opt-in cubic source-load replay on unchanged original mode3 stage/SSPRK3.
Separate from original A0/A1/C0/C1 identities. Source-off is original drive=0.
No claim of continuum sign, exterior null or physical acceptance.
"""
import argparse,hashlib,json,math,sys
from pathlib import Path
import numpy as np
from scipy.integrate import quad
import ksw668_f8_tt_multipole as original
from run_f8_common_clock_capture import configuration,T0,nt,dt,bulk,weight,required,observe
from run_f8_p0_native_receiver_state_capture import atomic_npz
from check_f8_source_dual_cubic import load
from check_f8_source_dual_primitive import EPS,volume


def run(label,work,budget,reference):
    assert label in ('cubic-A','cubic-C','off-A')
    key='C0' if label=='cubic-C' else 'A0';c=configuration(key,'common');dr=c['dr'];r=np.arange(math.ceil(c['r_outer']/dr)+1)*dr
    src_owner=original.exact_cell_averages;stage=original.stage
    if label=='off-A':
        src=src_owner(EPS,r,dr);c['drive']=0.
    else:
        src=np.zeros((3,len(r)))
        for i,d in enumerate((3,7,11)):
            l,_,_=load(dr,i);src[i,:len(l)]=l/volume(dr,len(l),d)
    end=float(r[np.flatnonzero(np.any(src!=0,axis=0))[-1]])+dr/2
    assert bulk-.012-math.log(12)>end
    sha=lambda x:hashlib.sha256(x).hexdigest();owners=('run_f8_cubic_source_intervention.py','check_f8_source_dual_cubic.py','check_f8_source_dual_primitive.py','run_f8_common_clock_capture.py','ksw668_f8_tt_multipole.py','ksw668_f8_fv_source_flux.py')
    identity=json.dumps(dict(label=label,config=c,source_sha256=sha(src.tobytes()),owners={p:sha(Path(__file__).with_name(p).read_bytes()) for p in owners}),sort_keys=True)
    work.mkdir(parents=True,exist_ok=True);ck=work/(label+'.npz');wp=work/(label+'.window.npz');seen={}
    if wp.exists():
        with np.load(wp,allow_pickle=False) as z:
            assert z['identity'].item()==identity;seen={int(i):v for i,v in zip(z['indices'],z['observations'])}
    if ck.exists():
        with np.load(ck,allow_pickle=False) as z:
            cursor=int(z['cursor'].item());assert json.loads(z['identity'].item())['arrays'][0]==sha(src.tobytes())
        assert all(i in seen for i in required if i<cursor),'missing prior window samples'
    def source(eps,rg,h):
        assert eps==EPS and h==dr and np.array_equal(rg,r);return src.copy()
    def monitored(U,P,M,outU,outP,outM,dr,dy,b,v,amp,sources,cp,cm,normal_order):
        stage(U,P,M,outU,outP,outM,dr,dy,b,v,amp,sources,cp,cm,normal_order)
        f=sys._getframe(1);l=f.f_locals;i=l.get('it',-1)
        if f.f_code.co_name=='propagate' and i in required and l.get('U') is U and l.get('P') is P and l.get('M') is M:
            assert amp==0. and normal_order==3 and i not in seen
            seen[i]=np.stack([observe(U,P,M,outU,outP,outM,dr,dy,b,v,rx,EPS) for rx in (bulk-.012,bulk+.1)])
    original.exact_cell_averages=source;original.stage=monitored
    try:
        try:prod=original.propagate(**c,checkpoint=ck,budget=budget,checkpoint_every=16)
        except InterruptedError as e:print(e,flush=True);return 75
    finally:
        original.exact_cell_averages=src_owner;original.stage=stage
        if seen:atomic_npz(wp,identity=identity,indices=np.array(sorted(seen)),observations=np.stack([seen[i] for i in sorted(seen)]))
    assert prod['steps']==nt and prod['step_time']==dt and sorted(seen)==required
    norm=quad(lambda x:math.exp(1-1/(1-x*x)),-1,1,epsabs=1e-13)[0]*.1
    weights=np.array([weight(T0+i*dt)*dt/norm for i in required]);obs=np.stack([seen[i] for i in required]);window=np.einsum('i,ipkrm->pkrm',weights,obs)
    assert np.isfinite(window).all()
    if label=='off-A':
        assert np.count_nonzero(obs)==0
        with np.load(ck,allow_pickle=False) as z:assert all(np.count_nonzero(z[k])==0 for k in ('U','P','M','w0','w1','w2','w3'))
        comparison=None
    else:
        rr=json.loads(reference.read_text())['results']['fine' if label=='cubic-C' else 'coarse']['rows'];expected=np.array([x['cubic'] for x in rr]);actual=window[0,1,0];scale=np.array([x['absolute'] for x in rr]);err=abs(actual-expected)/np.maximum(scale,1e-300);assert err.max()<2e-9,(expected,actual,err)
        comparison=dict(expected=expected.tolist(),actual=actual.tolist(),max_scaled_error=float(err.max()))
    result=dict(scope='original mode3 forward, explicit opt-in cubic source intervention or original source-off; no continuum certification',identity=json.loads(identity),source_support_end_with_halfcell=end,window_samples=len(required),weight_sum=float(weights.sum()),window_rows=['E4','legacy4','direct','SMS','F','R'],window_packets=['raw_stage_time','parity_stage_time'],places=['near','far'],window_signed=window.tolist(),source_off_exact_zero=label=='off-A',reverse_comparison=comparison,production=prod,checkpoint_sha256=sha(ck.read_bytes()),window_sha256=sha(wp.read_bytes()))
    (work/(label+'.json')).write_text(json.dumps(result,indent=2)+'\n');print(label,window.sum(axis=-1).tolist(),comparison,flush=True);return 0

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('label',choices=('cubic-A','cubic-C','off-A'));p.add_argument('--work',type=Path,default=Path('.local-f8-cubic'));p.add_argument('--reference',type=Path,default=Path('.local-f8-source-dual/source_cubic.json'));p.add_argument('--budget',type=float,default=12.);a=p.parse_args();assert 0<a.budget<=90;raise SystemExit(run(a.label,a.work,a.budget,a.reference))
