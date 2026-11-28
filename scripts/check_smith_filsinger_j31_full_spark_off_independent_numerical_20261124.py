#!/usr/bin/env python3
"""Independent SciPy diagnostics against J31 exact full spark-OFF enclosure.

This is NOT an interval proof: 9/9 state and 81/81 Jacobian membership
numerically cross-check the separately proved rational enclosure. No CI.
"""
from fractions import Fraction as F
import argparse,json
from pathlib import Path
import numpy as np
from scipy.integrate import solve_ivp
import check_smith_filsinger_j31_full_spark_off_four_slab_20261124 as r
try:
 import check_smith_filsinger_j31_source_15d_69d_shooting_20261124 as alt
 RHS=alt.mode_f;JAC=alt.mode_J
except ImportError:
 import check_smith_filsinger_j31_source_six_guard_shooting_20261124 as alt
 RHS=alt.f_mode;JAC=alt.jac_mode

def audit():
 original=r.smooth_leg()
 mode=tuple(original['mode'])
 clock=lambda box:float((F(box[0])+F(box[1]))/2)
 t0=clock(original['source_event_t0']);t1=clock(original['source_event_t1'])
 x0=np.array([float(F(v)) for v in r.src.STATES[2]],dtype=float)
 y0=np.r_[x0,np.eye(9,dtype=float).reshape(81)]
 def ode(t,y):
  X=y[:9];P=y[9:].reshape((9,9));return np.r_[RHS(t,X,mode),(JAC(X,mode)@P).reshape(81)]
 sol=solve_ivp(ode,(t0,t1),y0,rtol=2e-12,atol=1e-13,max_step=.0005)
 assert sol.success
 end=sol.y[:9,-1];Dx=sol.y[9:,-1].reshape((9,9))
 box=original['final_source_state_interval']
 matrix=original['full_smooth_flow_source_Dx_Phi_9x9_interval']
 valid_state=[F(lo)<=F(str(v))<=F(hi) for (lo,hi),v in zip(box,end)]
 valid_Dx=[F(matrix[i][j][0])<=F(str(Dx[i,j]))<=F(matrix[i][j][1])
       for i in range(9) for j in range(9)]
 assert all(valid_state) and all(valid_Dx)
 return dict(status='PASS_J31_INDEPENDENT_NUMERICAL_MEMBERSHIP_9_STATE_81_DX_ONLY',
  source_equation_numerical_backend='J31 independent 15D/69D SciPy source solver',
  original_exact_source_certificate_remains_the_authority=True,
  member_state_coordinates=sum(valid_state),total_state_coordinates=9,
  member_Dx_entries=sum(valid_Dx),total_Dx_entries=81,
  numeric_ode_steps=len(sol.t),finite_difference_derivative_claim=False,
  original_full_seven_segment_interval_DF_proved=False,
  periodic_orbit_proved=False,github_ci=False)

def main():
 p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args()
 d=audit();a.out.parent.mkdir(parents=True,exist_ok=True)
 a.out.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d,indent=2))
if __name__=='__main__':main()
