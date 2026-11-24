#!/usr/bin/env python3
"""Numerical (NOT rigorous) 18-boundary directional DP ball audit."""
import json
import numpy as np
from pathlib import Path
from independent_full_period_numerical_audit import root0
from independent_full_period_monodromy_audit import hybrid_tangent

end,M,salts,on=hybrid_tangent(root0)
C=np.linalg.inv(np.eye(9)-M)
D=end-root0
r=1e-7
errs=[]
for j in range(9):
 for sign in (-1,1):
  x=root0.copy();x[j]+=sign*r
  xx,Mxx,ss,chi=hybrid_tangent(x)
  derr=np.linalg.norm(Mxx-M,np.inf)
  q=np.linalg.norm(np.eye(9)-C@(np.eye(9)-Mxx),np.inf)
  errs.append(dict(coordinate=j,sign=sign,Jacobian_inf_variation=float(derr),q=float(q),periodic_modestatus=bool(chi),saltation_times=[u['t'] for u in ss]))
print('candidate norm inverse',np.linalg.norm(C,np.inf))
print('center correction',np.linalg.norm(C@D,np.inf))
print('max sampled DP variation',max(z['Jacobian_inf_variation'] for z in errs))
print('max sampled q',max(z['q'] for z in errs))
print('ball residual budget',r*(1-max(z['q'] for z in errs)))
p=Path(__file__).resolve().parents[1]/'Artifacts/smith-filsinger/full_period_ball_probe_diagnostic_20261124.json'
p.write_text(json.dumps(dict(status='NUMERIC_SAMPLES_ONLY_NOT_INTERVAL_PROOF',radius=r,centre_return_defect_inf=float(np.linalg.norm(D,np.inf)),center_preconditioned_defect_inf=float(np.linalg.norm(C@D,np.inf)),C_norm_inf=float(np.linalg.norm(C,np.inf)),worst_sampled_jacobian_variation=float(max(z['Jacobian_inf_variation'] for z in errs)),worst_sampled_preconditioned_q=float(max(z['q'] for z in errs)),samples=errs,derivative_uniform_bound_proved=False,banach_fixed_point_proved=False),indent=2)+'\n')
