#!/usr/bin/env python3
"""J34: source-labelled 69D admission ledger, exact original guards and J33 flow.

The first 9 state matches and six guard equations have exact source interval
rows. Other 54 flow rows are UNKNOWN, not zero: fail closed before Krawczyk.
An optional independent 69D/15D numerical source audit does not promote them.
Original Smith/Filsinger 9D synthetic prescribed-source circuit; no hardware.
"""
import argparse,hashlib,json
from pathlib import Path
from fractions import Fraction as F
import check_smith_filsinger_j31_native_seven_shortcharts_interval_20261124 as s

I=s.I
GUARD_NAMES=('V_ON','SPARK_OFF','SPARK_ON','U_ON','V_OFF','U_OFF')
PRE_SIGNS=(1,-1,1,1,-1,-1)
N=69
SOURCE_RECEIPT_SHA256='1736f652288fd77bfc165fc86eadb268fc94418c9024e19591a70bc08a4beb3b'

def iv(x):
 if isinstance(x,I):return x
 if isinstance(x,(tuple,list)):
  assert len(x)==2
  return I(F(x[0]),F(x[1]),raw=True)
 return I(F(x))

def check(f,what):
 if not f:raise AssertionError(what)

def axis_source():
 states=[[F(x) for x in row] for row in s.STATES]
 times=[F(0)]+[F(t) for t in s.TIMES[1:]]
 check(len(states)==7 and len(times)==7,'7 original chart states/clocks')
 check(all(times[k]<times[k+1] for k in range(6)),'original strict physical event order')
 check(s.PARAM['Vd']==F(1,10) and s.PARAM['Rd']==F(12,100),'original diode guard threshold/conductance changed')
 check(tuple(s.MODES)==((0,0,1),(0,1,1),(0,1,0),(0,1,1),(1,1,1),(1,0,1),(0,0,1)), 'actual source mode identity changed')
 return states,times

def norm_guard(k):
 r=[F(0)]*9
 if k in (0,4):r[3],r[4]=F(1),-F(1)
 elif k in (3,5):r[2],r[4]=F(1),-F(1)
 else:r[4]=F(1)
 return r

def source_exact(j33_path,state_radius=F(1,10**6),clock_radius=F(1,200000)):
 p=Path(j33_path);raw=p.read_bytes()
 check(hashlib.sha256(raw).hexdigest()==SOURCE_RECEIPT_SHA256,'J33 source result bytes not pinned')
 d=json.loads(raw)
 check(d['status']=='PASS_J33_COFRAME_INITIAL_0_TO_EVENT1_CONDITIONAL_SOURCE_NOT_69D','J33 wrong status')
 check(d['N']==256 and d['strict_picard_slabs']==256 and d['chronological_PB6_slabs']==256,'J33 insufficient fulltime source proof')
 check(d['signed_V_guard_negative_slabs']==255 and d['positive_V_slope_suffix_slabs']==1 and d['U_OFF_entire_time'] and d['spark_ON_entire_time'],'J33 original physical branch unvalidated')
 check(d['fixed_start_clock']=='0' and d['original_J29_event1_root_bracket_inside'],'wrong original absolute clock')
 check(d['original_event1_zero_guard_root_proved'] is False and d['original_69D_Krawczyk'] is False,'producer silently promoted root')
 states,times=axis_source()
 check(F(0)<state_radius<=F(1,10000),'source J33 x0 input radius containment')
 check(F(0)<clock_radius<=F(1,200000),'source J33 event1 clock containment')
 # Need each J34 event-time interval to be contained in its genuine J29/J30 bracket exterior.
 t_r=[clock_radius]*6
 t_r[5]=F(1,5000)  # event6 J30 bracket requires its actual wide independent clock domain
 for k in range(6):
  lo,hi=map(F,s.BRACKETS[k]);tc=times[k+1]
  check(tc-t_r[k]<lo<hi<tc+t_r[k],f'original exact root time bracket not included k{k+1}')
 # This check may force a larger radius than the proposed 1e-7 for k3,4,5,6.
 box=[I(v-state_radius,v+state_radius) for row in states for v in row]+[I(t-r,t+r) for t,r in zip(times[1:],t_r)]
 F69=[None]*69;DF69=[None]*69
 # Original 69D multiple shooting: nine blocks for h0..h5 plus nine
 # closure rows, guards at rows 63..68. Never silently fill unknown flow.
 missing_flow_owners=[
  ('event1_to_event2',9,18,'Artifacts/smith-filsinger/j31_two_track_full_v_on_spark_off_64_slab_receipt_20261124.json'),
  ('event2_to_event3',18,27,'Artifacts/smith-filsinger/j31_full_spark_off_four_slab_source_20261124.json'),
  ('event3_to_event4',27,36,'Artifacts/smith-filsinger/j32_event3_to_event4_signed_taylor_128slab_20261124.json'),
  ('event4_to_event5',36,45,'Artifacts/smith-filsinger/j31_two_track_full_uv_on_32_slab_receipt_20261124.json'),
  ('event5_to_event6',45,54,'Artifacts/smith-filsinger/j32_event5_to_event6_signed_taylor_128slab_20261124.json'),
  ('event6_to_exact_tau_return',54,63,'Artifacts/smith-filsinger/j32_event6_broad_source_to_exact_tau_128slab_20261124.json')]
 # Real source-certified original first leg: h0 = original y1 - source Φ0(x0,t1).
 end=[iv(v) for v in d['full_source_terminal_9D']]
 dx=[[iv(z) for z in row] for row in d['full_9x9_source_Dx_independent_event_clock']]
 dt=[iv(z) for z in d['full_event1_clock_partial_9D']]
 check(len(end)==9 and len(dx)==9 and all(len(row)==9 for row in dx) and len(dt)==9,'source original J33 tangent/clock shape')
 for i in range(9):
  F69[i]=box[9+i]-end[i]
  row=[I(0) for _ in range(69)]
  for j in range(9):row[j]=-dx[i][j]
  row[9+i]=I(1)
  row[63]=-dt[i] # original event1 terminal clock
  DF69[i]=row
 # Six original named physical guard equations are affine in original y1..y6,
 # and thus have exact 69D interval Jacobian regardless of the flow producer.
 local_slope=[];guard_boxes=[];negative_controls={}
 for k in range(6):
  j=k+1
  Y=[box[9*j+i] for i in range(9)]
  G=iv(s.guard(k,Y));guard_boxes.append(G)
  F69[63+k]=G
  row=[I(0) for _ in range(69)]
  gn=norm_guard(k)
  for i in range(9):row[9*j+i]=I(gn[i])
  DF69[63+k]=row
  # Transversality at the *same physical event clock* and the original PRE mode.
  T=box[63+k]
  pre=s.f(Y,T,s.MODES[k])
  speed=iv(s.guard_slope(k,pre))
  check(speed.a>0 if PRE_SIGNS[k]==1 else speed.b<0,f'original physical event{k+1} transversality not strict')
  check(G.a<=0<=G.b,f'original guard zero infeasible on proposed common box {k+1}')
  local_slope.append(speed)
 # A source mismatch and a reversed physical guard sign must be detected.
 check(all(F69[i].a<=0<=F69[i].b for i in range(9)),'first physical source matching cannot reach zero on J34 common box')
 wrong=box[9]+F(1,10)-end[0]
 check(wrong.a>0,'negative control: deliberately moved event1 must fail original source match')
 wrong_guard=(box[9+3]-box[9+4]+F(1,10))
 check(wrong_guard.a>0,'negative control: wrong V-on offset should not contain zero')
 # For every exact certified row, each coefficient is a genuine original-source
 # interval. All remaining 54 rows are explicitly missing, not constants/zeros.
 certified_rows=[i for i,r in enumerate(DF69) if r is not None]
 check(certified_rows==list(range(9))+list(range(63,69)),'wrong source-certified 69D row partition')
 return dict(source_kind='ORIGINAL_J31_J33_SYNTHETIC_NINE_STATE',status='PASS_ORIGINAL_SOURCE_15_OF_69_INTERVAL_ROWS_REMAINING_54_FAIL_CLOSED',
  original_modes=[list(m) for m in s.MODES],original_six_guard_names=list(GUARD_NAMES),
  indexed_state_origin='J23/J24 original source x0..x6',
  state_radius=str(state_radius),event_time_radii=[str(x) for x in t_r],common_nonzero_box=True,
  source_first_leg_receipt_sha256=SOURCE_RECEIPT_SHA256,
  validated_original_first_leg_9D_flow_rows=9,
  exactly_affine_original_six_guard_rows=6,
  verified_original_pre_switch_guard_slope_signs=6,
  strict_original_69D_Krawczyk_rows=0,
  certified_original_69D_F_DF_rows=15,
  original_69D_missing_F_DF_rows=54,
  missing_source_full_flow_rows=[dict(segment=k,rows=list(range(a,b)),committed_compact_receipt=p,requires_full_outward_F_and_9x9_Dx_Phi_and_time_partials=True) for k,a,b,p in missing_flow_owners],
  residual_interval_rows={str(i):F69[i].record() for i in certified_rows},
  jacobian_interval_rows={str(i):{str(j):z.record() for j,z in enumerate(DF69[i]) if z.a!=0 or z.b!=0} for i in certified_rows},
  physical_guard_slopes=[z.record() for z in local_slope],
  original_six_guard_boxes=[z.record() for z in guard_boxes],
  source_first_matching_zero_compatible=True,
  all_six_guard_zero_boxes_compatible=True,
  deliberately_shifted_source_match_rejected=True,
  deliberately_wrong_guard_offset_rejected=True,
  nonzero_ball_full_source_DF69=False,
  global_Krawczyk_attempted=False,
  original_six_guard_zero_equalities_jointly_proved=False,
  exact_periodic_orbit=False,
  numerical_seam_data_not_used_as_exact_source_evidence=True,
  original_J24_sixth_narrow_state_box_unpaid=True)

def main():
 a=argparse.ArgumentParser();a.add_argument('--j33',type=Path,required=True);a.add_argument('--out',type=Path,required=True);a.add_argument('--state-radius',default='0.000001');a.add_argument('--time-radius',default='0.000005');args=a.parse_args()
 data=source_exact(args.j33,F(args.state_radius),F(args.time_radius))
 args.out.parent.mkdir(parents=True,exist_ok=True);args.out.write_text(json.dumps(data,indent=2)+'\n')
 print(json.dumps({k:v for k,v in data.items() if k in ['status','certified_original_69D_F_DF_rows','original_69D_missing_F_DF_rows','verified_original_pre_switch_guard_slope_signs','strict_original_69D_Krawczyk_rows']},indent=2))
if __name__=='__main__':main()
