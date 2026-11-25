#!/usr/bin/env python3
"""J35 exact-rational *conditional* reverse solve for original J31/J34 geometry.

A 9x9 rational return-map matrix M0 and metric P were suggested using
original-source independent numerical integration. The source itself is
NOT thereby rigorously enclosed. All statements in this producer are
algebraic exact-rational implications and original J29/J30 bracket budgets.
Actual Filsinger 69D source periodic orbit remains OPEN.
"""
import base64,hashlib,json,zlib,argparse
from fractions import Fraction as F
from pathlib import Path
import check_smith_filsinger_j31_native_seven_shortcharts_interval_20261124 as s
PACKED=(
 'eNplVkuu2zAMvEvWzwj/FHuHAt0HOUnRu5dWYluk3ypPsMiZ4XDsv4/f8Pj1ej3YeQgTPxG+f4+fBxKgOkc5FMUBEk+9jjYEART2etvFcOD6oBBFK6eOIfyk64Tdn0Z61M5fiufB++f12DQC4kl6ATBDJPIKSvMoooFCd0evPDdyoKPgvMooYZVjCOUh1ovsVJGg4HBZKe6ISZShaQumZqPWY8ahUCQbAZRwymMhIVYfw6DQRLeKQuyIo8IjX6Y0qeYzqt4BDwGS0mFjEIEsh996e7kkwPwdzqw2EkQfcdrKSblcpIAcQhlXKIq0wQhZNI3SbESIDfCkZecQDB2kiebCKVJDBjTqAMlNRaW6JgDG8JXANn1khVR2aBaknNJkXrCmW7NcZ5VMpSmuu32j+4YBUuBlYdByr3Cd6hgpALm3TbMwbQIPV2nj8lz5REdF3iSGOue8VzILHdEJ5PDTDKuWGQkSfdc4k6Z6UAf4YO7pwa4rjv1uaHMIs3n120dhcFRvuzossMtOjLq7Yg0p49tjNnxmTjmMyCw8DPCJqqFYdpA9kiutQwDAyzQTLI6MmwZ2xJ4DtGxCGAsWC2aWCmNzZbhzFS1BzmhYKAZmIBUPEXCzBiOTLHZ+v38efz4vC0zHGZ2IPy+FK1N3mmTl/40EviJPw6oeeOZkkD7umkC+Au6/DyKTmp1jmrL1lpnsoNfcpq/E42rD54tlWhOPaX7MCzJWQqa03jXzBQqBHeJNKDe2tXEuHiAvfAfpESY7cM21XHtvGSQR60GGWcp9Gk3Ul2p2ZfzHT0Xrwrp13rPO8Kqr+7KehSnjTVc9+VzRWcpWiBZHFE4MbcJV7Rvh2tc4jb1ezkDGIkeutusi8Dbj73oJhSw+mJKsDrsP+yb4jfoNw/5twVyK5MvQbEUVuXaXuMiZ+RXW6vVmuD7yqv1NgN47IzaDcpzLV8ig4f71UJAsm1a8Xq1WZ95kr3R70zwnLLXOT8NvCi773Xasmby47Tbvm9I3wrX5Ds1hnNDe73//AYB7F/A=')
JSON_SHA='e4f0426aa82786146b5c5725425afe7f036867bcd394e576cee7d687dee4b8e4'

def load_candidate():
 raw=zlib.decompress(base64.b64decode(PACKED))
 assert hashlib.sha256(raw).hexdigest()==JSON_SHA
 d=json.loads(raw)
 return ([[F(c) for c in r] for r in d['M0']],[[F(c) for c in r] for r in d['P0']])

def trans(A):return [list(r) for r in zip(*A)]
def mm(A,B):return [[sum((x*y for x,y in zip(row,col)),F(0)) for col in zip(*B)] for row in A]
def mat_sub(A,B):return [[x-y for x,y in zip(a,b)] for a,b in zip(A,B)]
def rownorm(A):return max(sum(map(abs,row),F(0)) for row in A)
def colnorm(A):return rownorm(trans(A))
def sym(A):return all(A[i][j]==A[j][i] for i in range(len(A)) for j in range(len(A)))
def gersh_lower(A):return min(A[i][i]-sum((abs(A[i][j]) for j in range(len(A)) if i!=j),F(0)) for i in range(len(A)))
def gersh_upper(A):return max(A[i][i]+sum((abs(A[i][j]) for j in range(len(A)) if i!=j),F(0)) for i in range(len(A)))

def ldl_pos(A):
 assert sym(A)
 n=len(A);D=[];L=[[F(int(i==j)) for j in range(n)] for i in range(n)]
 for i in range(n):
  t=A[i][i]-sum((L[i][k]**2*D[k] for k in range(i)),F(0))
  assert t>0,('non-SPD pivot',i,t)
  D.append(t)
  for j in range(i+1,n):
   L[j][i]=(A[j][i]-sum((L[j][k]*L[i][k]*D[k] for k in range(i)),F(0)))/t
 return D

def prove():
 M,P=load_candidate()
 assert len(M)==len(P)==9 and all(len(z)==9 for z in M+P)
 assert sym(P)
 R=mat_sub(P,mm(trans(M),mm(P,M)))
 assert sym(R)
 p_piv=ldl_pos(P);r_piv=ldl_pos(R)
 Pmin=gersh_lower(P);Pmax=gersh_upper(P);Rmin=gersh_lower(R)
 assert Pmin>F(1,4) and Pmax<F(7) and Rmin>F(99,100)
 eps=F(1,20)
 E_bound=eps*(colnorm(M)*rownorm(P)+colnorm(P)*rownorm(M))+eps*eps*rownorm(P)
 assert E_bound<F(41,50),('source matrix robustness budget failed',E_bound)
 assert F(99,100)-F(41,50)>F(1,6)
 # If every actual D Poincare(x) is within ||M_actual-M||_1,∞ <= 1/20,
 # then P-M_actual^T P M_actual is >= I/6, via exact operator bounds.
 # P <= 7 I implies ||D Poincare||_P^2 <= 41/42 < (99/100)^2.
 assert F(41,42)<F(99,100)**2
 rP=F(1,10**7)
 # P >= I/4 implies |delta x_i| <= 2 rP for a P-ellipsoid.
 rx=2*rP
 assert rx<=F(1,5000000)
 L_time=[10,20,20,10,4,40]  # target source-validated L1 norms, NOT achieved yet
 L_state=[50,150,150,10,10,10]  # target event state Jacobian row norms
 times=[F(z) for z in s.TIMES[1:]]
 budgets=[]
 for k in range(6):
  left,right=map(F,s.BRACKETS[k]);cent=times[k]
  h=F(1,200000) if k<5 else F(1,5000)
  assert left<right and cent-h<left<right<cent+h
  bracket_offset=max(abs(cent-left),abs(right-cent))
  margin=h-bracket_offset
  time_shift=L_time[k]*rx
  assert time_shift<margin,('actual source time budget fails',k,margin,time_shift)
  state_shift=L_state[k]*rx
  if k<5: assert state_shift<F(1,10000)
  budgets.append(dict(event=k+1,event_time_center=str(cent),exact_source_bracket=[str(left),str(right)],
   nominal_root_bracket_max_offset=str(bracket_offset),physical_clock_halfwidth=str(h),
   admissible_clock_extra_margin=str(margin),
   target_certified_event_time_l1_derivative_upper=L_time[k],
   conditional_physical_event_time_shift_upper=str(time_shift),
   target_certified_event_state_Dx_inf_upper=L_state[k],
   conditional_event_state_coordinate_shift_upper=str(state_shift),
   real_source_derivative_bounds_proved_here=False))
 # If strict centre ||Poincare(x*)-x*||_P < 1e-10 and q < 99/100,
 # the P-ball radius 1e-7 is inward under true event-admitted return.
 center_target=F(1,10**10)
 assert center_target<(1-F(99,100))*rP
 # deliberately conservative checks; no D Poincare source interval supplied.
 return dict(status='PASS_EXACT_RATIONAL_CONDITIONAL_9D_LYAPUNOV_AND_SIX_SOURCE_BRACKET_BUDGETS_NOT_PERIODIC_ORBIT',
  source_model='ORIGINAL_SMITH_FILSINGER_9D_SYNTHETIC_J23_J34',
  source_M0_numeric_proposal_not_rigorously_certified=True,
  exact_candidate_matrix_m=9,exact_rational_symmetric_P=True,
  exact_LDL_positive_P_pivots=9,exact_LDL_positive_R_pivots=9,
  exact_P_min_gersh=str(Pmin),exact_P_max_gersh=str(Pmax),exact_R_min_gersh=str(Rmin),
  P_greater_than_I_over_4=True,P_less_than_7I=True,R0_greater_than_99_over_100_I=True,
  exact_M0_norm_1=str(colnorm(M)),exact_M0_norm_inf=str(rownorm(M)),
  exact_P_norm_1=str(colnorm(P)),exact_P_norm_inf=str(rownorm(P)),
  target_source_D_Poincare_distance_1_and_inf=str(eps),
  exact_source_derivative_perturbation_algebra_upper=str(E_bound),
  exact_strict_candidate_contraction_bound_Q='99/100',
  actual_original_ODE_Poincare_derivative_proved_within_tolerance=False,
  exact_P_ellipsoid_radius=str(rP),exact_coordinate_projection_radius=str(rx),
  proposed_source_centre_P_norm_return_residual_target=str(center_target),
  actual_original_P_norm_centre_residual_certified=False,
  original_J29_J30_six_bracket_real_clock_remaining_budgets=budgets,
  source_guard_time_derivative_targets_certified=False,
  source_event_state_derivative_targets_certified=False,
  sixth_J24_narrow_state_box_unpaid=True,
  all_six_conditional_guard_monotonicity_on_common_ellipsoid_proved=False,
  original_source_69D_F_DF_full_certificate=False,
  source_69D_Krawczyk_rows_proved=0,exact_periodic_orbit=False,
  original_hardware_energy_metrology_proved=False)

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True)
 args=p.parse_args();d=prove();args.out.parent.mkdir(parents=True,exist_ok=True)
 args.out.write_text(json.dumps(d,indent=2)+'\n')
 print(json.dumps({k:v for k,v in d.items() if k in ('status','exact_P_min_gersh','exact_P_max_gersh','exact_R_min_gersh','exact_source_derivative_perturbation_algebra_upper','actual_original_ODE_Poincare_derivative_proved_within_tolerance')},indent=2))
