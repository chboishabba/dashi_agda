"""Original safe-clock A0/A1/C0/C1 completed matrix receipt.
Keep per-mode signs, capture identities, and off-shell Weyl residuals.
Finite replay/correspondence only; no continuum sign or error certificate.
"""
import argparse,hashlib,json,math
from pathlib import Path
import numpy as np
from check_f8_p0_original_same_clock_state import read
from check_f8_parity_capture_tail import capture
from run_f8_safe_source_capture import configuration

LABELS=('A0','A1','C0','C1')
SUFFIXES=('mode_intrinsic_4D_electric_Weyl','mode_projected_5D_electric_Weyl','mode_intrinsic_4D_electric_Weyl_tangent','mode_projected_5D_electric_Weyl_tangent')
PACKETS=('raw','even','characteristic','even_stage_time')
ROWS=('E4','legacy4','direct','SMS','F','R')

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def report(work):
    runs={};count=0;worst=0.;maxpar=0.
    for label in LABELS:
        paths={k:work/(label+s) for k,s in [('production','.json'),('checkpoint','.npz'),('sidecar','.receiver-state.npz'),('packets','.packets.json')]}
        cfg=configuration(label);p=json.loads(paths['production'].read_text());d=read(paths['checkpoint'],paths['sidecar'],paths['production']);packet=capture(paths['checkpoint'],paths['sidecar'],paths['production'])
        assert packet==json.loads(paths['packets'].read_text()),'stored packet differs from replay'
        with np.load(paths['checkpoint'],allow_pickle=False) as z:
            identity=json.loads(z['identity'].item());cursor=int(z['cursor'].item());assert cursor==p['steps']+1
        with np.load(paths['sidecar'],allow_pickle=False) as z:
            meta=json.loads(z['metadata'].item())
            U,P,M,Ut=(z[k] for k in ('U','P','M','Ut'))
            Q=(P[:,1:-1,:]-M[:,1:-1,:])/2-(U[:,2:,:]-U[:,:-2,:])/(2*p['step_bulk'])
            interior_Q=float(np.max(abs(Q)))
        assert identity['config']['weak_source_load']==cfg['weak_source_load']
        assert p['step_radial']==cfg['dr'] and p['step_bulk']==cfg['dy'] and p['step_time']<=cfg['dt']
        assert p['step_time']*(7/cfg['dr']+10/cfg['dy']+400)<=.9+1e-15
        out={}
        for place,prefix in [('near','receiver'),('far','far')]:
            original=np.array([p[prefix+'_'+k] for k in SUFFIXES]);assert original.shape==(4,3);count+=original.size
            v=packet['receivers'][place];a=np.array([v['observations'][k] for k in PACKETS]);assert a.shape==(4,6,3)
            assert np.isfinite(a).all() and np.isfinite(original).all()
            t=p['receiver_t'];r=a[:,2]-a[:,3]+(1/t+1/(2*t**3))*a[:,4]+a[:,5]/(3*t*t)
            scale=np.abs(a[:,2])+np.abs(a[:,3])+(1/t+1/(2*t**3))*np.abs(a[:,4])+np.abs(a[:,5])/(3*t*t)
            rel=float(np.max(abs(r)/np.maximum(scale,1e-300)));worst=max(worst,rel);assert rel<1e-12
            np.testing.assert_allclose(a[0,[0,3]],original[[2,3]],rtol=1e-9,atol=1e-12)
            maxpar=max(maxpar,*v['parity_identity_remainders'])
            out[place]=dict(original=original.tolist(),observations=a.tolist(),raw_minus_even_normal_jets=v['raw_minus_even_normal_jets'],stage_minus_central_Wt=v['stage_minus_central_Wt'],interior_Q_receiver=v['interior_Q_receiver'],interior_Qdot_receiver=v['interior_Qdot_receiver'],parity_identity_remainders=v['parity_identity_remainders'],radial_ids=v['radial_ids'],mode_H=d['receivers'][place]['mode_H'],mode_Q_wall=d['receivers'][place]['mode_Q_wall'],mode_G_wall=d['receivers'][place]['mode_G_wall'],relative_offshell_identity_error=rel)
        runs[label]=dict(identity=identity,meta=meta,cursor=cursor,sha256={k:sha(v) for k,v in paths.items()},interior_Q_max=interior_Q,receivers=out)
    assert count==96
    return dict(scope='actual original mode3 safe-clock source-on runs; capture replay, signed finite observations, not convergence or physical acceptance',original_rows=list(SUFFIXES),packet_names=list(PACKETS),packet_rows=list(ROWS),multipoles=[0,2,4],original_signed_count=count,max_scaled_offshell_identity_error=worst,max_parity_identity_remainder=maxpar,runs=runs)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--work',type=Path,required=True);a=p.parse_args();print(json.dumps(report(a.work),indent=2))
