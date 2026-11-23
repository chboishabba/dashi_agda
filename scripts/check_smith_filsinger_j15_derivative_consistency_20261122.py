#!/usr/bin/env python3
"""J15 source-indexed fixed-switch-regime finite-difference consistency audit.
Requires J12 committed source. Synthetic model only; not device measurements.
Run from scripts/ directory: python check_smith_filsinger_j15_derivative_consistency_20261122.py
"""
import json,numpy as np
from check_smith_filsinger_j12_restored_cycles_20261122 import BASE,periodic
P=BASE|dict(Von=.003,Voff=.0009,source_amp=.1)
OBS=['driver','incident','outgoing','spark','diode']
PARAM=['source_amp','phase','k','Von','Vd']
STEP={'source_amp':.005,'phase':.08,'k':.005,'Von':.00015,'Vd':.005}
def experiment(factor):
 cols=[];counts=[];max_residual=0;max_closure=0
 for name in PARAM:
  h=STEP[name]*factor
  def go(sign):
   p=P if name=='phase' else P|{name:P[name]+sign*h}
   phase=.3+sign*h if name=='phase' else .3
   z=periodic(p,True,phase,max_iter=28,tol=2e-6)
   assert abs(z['residual'])<1e-6 and z['closure']<2e-6 and abs(z['storage_delta'])<1e-5
   return z
  a,b=go(1),go(-1)
  counts.append([a['switches'],b['switches']])
  max_residual=max(max_residual,abs(a['residual']),abs(b['residual']))
  max_closure=max(max_closure,a['closure'],b['closure'])
  cols.append([(a[k]-b[k])/(2*h) for k in OBS])
 J=np.array(cols).T
 rows=np.maximum(np.max(abs(J),axis=1),1e-12)
 columns=np.maximum(np.linalg.norm(J/rows[:,None],axis=0),1e-12)
 S=np.linalg.svd((J/rows[:,None])/columns[None,:],compute_uv=False)
 return dict(factor=factor,jacobian=J.tolist(),switch_counts=counts,
             same_counts=all(a==b for a,b in counts),relative_singular_values=(S/S[0]).tolist(),
             rank_cutoff_1e_5=int(np.sum(S/S[0]>1e-5)),
             max_residual=max_residual,max_closure=max_closure)
def main():
 results=[experiment(f) for f in [.25,.5,1.]]
 changes=[]
 for a,b in zip(results,results[1:]):
  A=np.array(a['jacobian']);B=np.array(b['jacobian'])
  changes.append(dict(factors=[a['factor'],b['factor']],
     relative_frobenius_difference=float(np.linalg.norm(B-A)/max(np.linalg.norm(A),1e-15))))
 assert all(z['same_counts'] and z['rank_cutoff_1e_5']==5 for z in results)
 # The stability requirement is a separate diagnostic, not assumed by selected cutoff.
 print(json.dumps(dict(results=results,changes=changes,
     boundary='rank-5 at cutoff is NOT derivative convergence or measured physical identifiability',
     source='conditional synthetic S3/S5'),indent=2))
if __name__=='__main__':main()
