#!/usr/bin/env python3
"""J16 restored-cycle event-order and small-step derivative audit.
Conditional S3/S5 synthetic model, not Filsinger physical evidence.
Requires the J16 event_log update to committed J12.
"""
import json,numpy as np
from check_smith_filsinger_j12_restored_cycles_20261122 import BASE,periodic
P=BASE|dict(Von=.003,Voff=.0009,source_amp=.1)
STEPS=dict(source_amp=.005,phase=.08,k=.005,Von=.00015,Vd=.005)
OBS=['driver','incident','outgoing','spark','diode']
def audit(scale):
 cols=[];details=[]
 for name,h0 in STEPS.items():
  h=scale*h0
  def simulate(sign):
   p=P if name=='phase' else P|{name:P[name]+sign*h}
   phase=.3+sign*h if name=='phase' else .3
   r=periodic(p,True,phase,max_iter=28,tol=2e-6)
   assert r['closure']<2e-6 and abs(r['residual'])<1e-6 and abs(r['storage_delta'])<1e-5
   return r
  minus,plus=simulate(-1),simulate(1)
  ea,eb=minus['event_log'],plus['event_log']
  sequence=[z[1] for z in ea]==[z[1] for z in eb]
  shift=max((abs(a[0]-b[0]) for a,b in zip(ea,eb)),default=0.) if len(ea)==len(eb) else None
  details.append(dict(parameter=name,minus_count=len(ea),plus_count=len(eb),
      matching_order=sequence,max_pairwise_event_time_shift=shift,
      minus_first_four=ea[:4],plus_first_four=eb[:4]))
  cols.append([(plus[k]-minus[k])/(2*h) for k in OBS])
 J=np.array(cols).T
 rows=np.maximum(abs(J).max(axis=1),1e-12)
 columns=np.maximum(np.linalg.norm(J/rows[:,None],axis=0),1e-12)
 sv=np.linalg.svd((J/rows[:,None])/columns[None,:],compute_uv=False)
 return dict(scale=scale,stencils=details,jacobian=J.tolist(),
     relative_singular_values=(sv/sv[0]).tolist(),rank_cutoff_1e_5=int(np.sum(sv/sv[0]>1e-5)))
if __name__=='__main__':
 results=[audit(.125),audit(.25)]
 A=np.array(results[0]['jacobian']);B=np.array(results[1]['jacobian'])
 delta=float(np.linalg.norm(B-A)/max(np.linalg.norm(A),1e-15))
 assert all(r['rank_cutoff_1e_5']==5 for r in results)
 assert all(x['matching_order'] for r in results for x in r['stencils'])
 result=dict(result='conditional local rank passes; ordered event-time smoothness certificate NOT established',
    scenarios=results,relative_jacobian_frobenius_change=delta,
    source_status='synthetic; not observed environmental RF or Filsinger netlist')
 print(json.dumps(result,indent=2))
