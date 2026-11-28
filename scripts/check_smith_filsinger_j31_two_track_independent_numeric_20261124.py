#!/usr/bin/env python3
"""Independent numerical membership only for J31 original 1->2 and 4->5 source legs."""
import argparse,json
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from scipy.integrate import solve_ivp
import check_smith_filsinger_j31_two_track_full_uv_on_20261124 as proof
import check_smith_filsinger_j31_source_six_guard_shooting_20261124 as donor

def audit(k):
 cert=proof.validate(k)
 a=float(F(proof.s.TIMES[k]));b=float(F(proof.s.TIMES[k+1]))
 x0=np.array(list(map(float,proof.s.STATES[k])),dtype=float)
 y0=np.r_[x0,np.eye(9).reshape(81)]
 mode=tuple(cert['original_mode'])
 def ode(t,y):
  v=y[:9];mat=y[9:].reshape(9,9)
  return np.r_[donor.f_mode(t,v,mode),(donor.jac_mode(v,mode)@mat).ravel()]
 out=solve_ivp(ode,(a,b),y0,rtol=2e-12,atol=1e-13,max_step=.0008)
 assert out.success
 state=out.y[:9,-1];jac=out.y[9:,-1].reshape(9,9)
 box=cert['final_state_interval'];M=cert['original_source_DxPhi_interval']
 okx=[F(lo)<=F(str(v))<=F(hi) for (lo,hi),v in zip(box,state)]
 okJ=[F(M[i][j][0])<=F(str(jac[i,j]))<=F(M[i][j][1]) for i in range(9) for j in range(9)]
 assert all(okx) and all(okJ)
 return {'segment':k,'original_mode':list(mode),'numeric_source_steps':len(out.t),
  'terminal_state_members':sum(okx),'total_terminal_states':9,
  'source_jacobian_members':sum(okJ),'total_jacobian_entries':81,
  'independent_SciPy_only_not_rigorous':True,'original_source_interval_certificate_external':True}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
 result={'status':'PASS_J31_TWO_NEW_LONG_LEGS_INDEPENDENT_NUMERICAL_SOURCE_MEMBERSHIP',
 'numerical_only':True,'global_source_69D_Krawczyk':False,
 'segments':[audit(1),audit(4)]}
 a.out.parent.mkdir(parents=True,exist_ok=True)
 a.out.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
