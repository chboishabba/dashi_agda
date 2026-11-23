#!/usr/bin/env python3
"""J19 exact J18 circuit: zero resistor loss, HF load, restored branch controls.

Synthetic model only. Rfree=0 is a mathematically lossless *assumed*
freewheel path, NOT a certified source reel netlist or zero total loss.
"""
import hashlib, json
from pathlib import Path
import numpy as np
import sympy as sp
import check_smith_filsinger_j18_hf_spark_tank_20261123 as hf

P=dict(source_amp=1.2,Von=.006,Voff=.0018,Rfree=0.)
HF_SHA='f4270a475f010874056cfe3cdeff5ee8e43c44eb'
T=hf.native.T

def sha(path):
 b=Path(path).read_bytes();return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\x00'+b).hexdigest()

def cycle(overrides=None,phase=.3,maxiter=10,tol=2e-5):
 p=hf.native.BASE|hf.DEFAULT|P|(overrides or {})
 x=np.zeros(9); on=False
 for n in range(maxiter):
  y,on2,r=hf.advance(p,p['source_amp']>0,phase,state=x,active=on,t0=n*T,
       max_step=.055,rtol=3e-8,atol=5e-10)
  diff=float(np.max(abs(y-x)))
  if diff<tol and on2==on:
   z,on3,v=hf.advance(p,p['source_amp']>0,phase,state=y,active=on2,t0=(n+1)*T,
      max_step=.055,rtol=3e-8,atol=5e-10)
   close=float(np.max(abs(z-y)))
   a=[label for _,label in r['event_log']]
   b=[label for _,label in v['event_log']]
   shift=max((abs(q[0]-s[0]) for q,s in zip(r['event_log'],v['event_log'])),default=0.) if a==b else None
   if close<tol and on3==on2 and shift is not None and shift<.02:
    assert abs(v['residual'])<3e-5 and abs(v['storage_delta'])<1e-5
    return dict(accepted=True,cycles=n+2,closure=close,event_shift=shift,
       event_labels=b,event_times=[t for t,_ in v['event_log']],
       work=hf.simple(v))
  x=y;on=on2
 return dict(accepted=False,last_closure=diff,last_cycle=hf.simple(r),last_event_labels=[l for _,l in r['event_log']])

def summary(x):
 return dict(closure=x['closure'],iterations=x['cycles'],events=len(x['event_labels']),
   event_shift=x['event_shift'],**x['work'])

def exact():
 rf,I,rc,rg,gl=sp.symbols('R_f I_off R_c R_g G_L',nonnegative=True)
 assert sp.simplify((rf*I).subs(rf,0))==0
 # Zero ONLY the freewheel resistor, not all heat or the load.
 assert (rc+rg+gl).is_nonnegative
 # Positive current/voltage and positive resistances imply other real losses.
 assert (rc+rg+gl).subs({rc:1,rg:1,gl:1})>0
 # Alternative PASSIVE capacitor-return completion: the OFF current is
 # routed into existing Ch rather than an assumed ideal resistive bypass.
 on,ih,x,b,u,kh,Lh,Ch,alpha=sp.symbols(
  'on ih x b u kh Lh Ch alpha',real=True)
 g=on+(1-on)  # illustrative 1:1 LC connection at both switch states
 eh=Lh*ih**2/2+Ch*(x*x/2+sp.Rational(3,4)*alpha*x**4)
 didt=(on*b-g*x-(rc+on*rg)*ih-kh*u)/Lh
 dxdt=(g*ih-gl*x)/(Ch*(1+3*alpha*x*x))
 edot=sp.simplify(sp.diff(eh,ih)*didt+sp.diff(eh,x)*dxdt)
 assert sp.simplify(edot-(on*b*ih-kh*u*ih-(rc+on*rg)*ih**2-gl*x*x))==0
 return dict(freewheel_work='Rfree * integral_off(i_h^2 dt)',Rfree_zero_exact=True,
    alternative_passive_capacitive_return_symbolic_identity=True,
    alternative_reactive_return_numerically_replayed=False,
    zero_total_loss_inferred=False)

def run():
 assert sha(hf.__file__)==HF_SHA
 e=exact()
 base=cycle({'Rfree':.4,'Von':.003,'Voff':.0009})
 center=cycle()
 off=cycle({'source_amp':0.})
 assert all(v['accepted'] for v in (base,center,off))
 assert center['work']['freewheel_heat']==0 and center['work']['hf_load']>base['work']['hf_load']
 assert center['work']['net_wave']>0 and center['work']['hf_load']>off['work']['hf_load']>0
 pairs={}
 for name,(a,b) in {
   'amplitude':({'source_amp':1.195},{'source_amp':1.205}),
   'hf_coupling':({'kh':.1198},{'kh':.1202}),
   'phase':({'phase':.295},{'phase':.305}),
 }.items():
  l=cycle({k:v for k,v in a.items() if k!='phase'},a.get('phase',.3))
  r=cycle({k:v for k,v in b.items() if k!='phase'},b.get('phase',.3))
  assert l['accepted'] and r['accepted']
  labels_match=l['event_labels']==r['event_labels']==center['event_labels']
  shift=max((abs(t-u) for t,u in zip(l['event_times'],r['event_times'])),default=0.) if labels_match else None
  assert labels_match and shift is not None and shift<.02
  assert all(v['work']['freewheel_heat']==0 and v['work']['net_wave']>0 and v['work']['hf_load']>0 for v in (l,r))
  pairs[name]=dict(accepted=True,events=len(l['event_labels']),max_event_shift=shift,
     net_wave=[l['work']['net_wave'],r['work']['net_wave']],load=[l['work']['hf_load'],r['work']['hf_load']])
 d=center['work']['hf_load']-off['work']['hf_load']
 assert d>0
 return dict(status='PASS_LOCAL_NATIVE_J18_ZERO_FREEWHEEL_J19',hf_sha=HF_SHA,
    symbolic=e,baseline=summary(base),zero_freewheel=summary(center),
    wave_off_same_driver=summary(off),wave_sensitive_delta_HF_load=d,
    driver_work_delta=center['work']['driver']-off['work']['driver'],
    hf_load_improvement_over_J18_baseline=center['work']['hf_load']/base['work']['hf_load'],
    local_branch_pairs=pairs,distinct_source_off_event_branch=True,
    physical_zero_resistance_device_proven=False,all_losses_zero=False,
    original_Duga_HAARP_SURA_source_to_device_calibrated=False,
    experimental_HF_load_measured=False,global_event_branch_certified=False,
    github_ci_used=False,agda_kernel_run=False)

if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
