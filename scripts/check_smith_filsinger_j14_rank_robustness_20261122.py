#!/usr/bin/env python3
"""J14 finite-difference audit of J13 restored-cycle inverse rank.
Synthetic dimensionaless comparison; requires J12 module and J13 JSON receipt.
"""
import json, numpy as np
from check_smith_filsinger_j12_restored_cycles_20261122 import BASE, periodic
OBS=['driver','incident','outgoing','spark','diode']
PARAMS=['source_amp','phase','k','Von','Vd']
BASELINE=BASE|dict(Von=.003,Voff=.0009,source_amp=.1)
PHASE=.3
STEPS=dict(source_amp=.005,phase=.08,k=.005,Von=.00015,Vd=.005)
def observe(p,phase):
 x=periodic(p,True,phase,max_iter=28,tol=2e-6)
 assert x['closure']<2e-6 and abs(x['residual'])<1e-6 and abs(x['storage_delta'])<1e-5
 return x
def relative_singular(J):
 rows=np.maximum(np.max(np.abs(J),axis=1),1e-12)
 columns=np.maximum(np.linalg.norm(J/rows[:,None],axis=0),1e-12)
 values=np.linalg.svd((J/rows[:,None])/columns[None,:],compute_uv=False)
 return values/values[0]
def sample(factor):
 columns=[];counts=[]
 for name in PARAMS:
  h=STEPS[name]*factor
  if name=='phase': a=observe(BASELINE,PHASE+h);b=observe(BASELINE,PHASE-h)
  else: a=observe(BASELINE|{name:BASELINE[name]+h},PHASE);b=observe(BASELINE|{name:BASELINE[name]-h},PHASE)
  counts.append([a['switches'],b['switches']])
  columns.append([(a[k]-b[k])/(2*h) for k in OBS])
 J=np.array(columns).T
 sv=relative_singular(J)
 return dict(step_factor=factor,relative_singular_values=sv.tolist(),
             rank_at_relative_1e_5=int(np.sum(sv>1e-5)),
             same_switch_count=[a==b for a,b in counts],
             switch_counts=counts,jacobian=J.tolist())
if __name__=='__main__':
 results=[sample(.5),sample(1.),sample(2.)]
 assert all(r['rank_at_relative_1e_5']==5 for r in results)
 assert all(results[0]['same_switch_count']) and all(results[1]['same_switch_count'])
 assert not all(results[2]['same_switch_count'])
 print(json.dumps(dict(status='conditional 3/3 rank cutoff checks PASS; doubled-step smoothness gate FAILS',
  scenarios=results,source='synthetic; conditional approximate restored cycles',
  interpretation='Five numerical rank directions at selected cutoff; weak singular value unstable, double-step crosses switching boundaries.'),indent=2))
