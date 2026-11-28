#!/usr/bin/env python3
"""J31 k4 U+V ON entire event4->5 via exact signed two-track source transport.

A central source solution uses rational Taylor2 endpoint enclosures, while
original box/time variation remains in a nonnegative componentwise Jacobi
majorant, NOT naively appended to independently re-centered interval boxes.
One full conditional physical leg is certified; NOT a periodic orbit or 69D.
"""
import argparse, json
from fractions import Fraction as F
from pathlib import Path
import check_smith_filsinger_j31_pb8_anisotropic_six_time_20261124 as pb
s=pb.src; I=s.I
N=32
DT=F('0.000005')
ZERO=F(0)

def validate(k=4):
 Nlocal=64 if k==1 else N
 assert k in (1,4)
 a=F(s.TIMES[k]);b=F(s.TIMES[k+1]);mode=s.MODES[k]
 assert mode==((0,1,1) if k==1 else (1,1,1))
 T0=I(a-DT,a+DT);T1=I(b-DT,b+DT)
 for j,T in ((k-1,T0),(k,T1)):
  lo,hi=map(F,s.BRACKETS[j]);assert T.a<lo<hi<T.b
 grid=[a+(b-a)*F(j,Nlocal) for j in range(Nlocal+1)]
 centre=[I(F(v)) for v in s.STATES[k]]
 initial=[I(F(v)-F('0.0001'),F(v)+F('0.0001')) for v in s.STATES[k]]
 variation=[F('0.0001')]*9
 # Exact source time-variation theorem: d(start_time)Phi=-P f(start);
 # initial extra is a conservative derivative bound for the local initial
 # clock variation, with an independently Picard-validated time extension.
 starttube=[I(F(v)-F('0.0005'),F(v)+F('0.0005')) for v in s.STATES[k]]
 fstart=s.f(starttube,T0,mode)
 left_box=[initial[i]+I(-DT,DT)*fstart[i] for i in range(9)]
 assert all(x.within(y) for x,y in zip(left_box,starttube))
 # The short virtual backward/forward source extension is itself Picard.
 f0_jac=s.fJ(starttube,T0,mode)[1]
 assert DT*max(sum(x.mag() for x in row) for row in f0_jac)<F(1)
 variation=[variation[i]+DT*fstart[i].mag() for i in range(9)]
 P=[[I(int(i==j)) for j in range(9)] for i in range(9)]
 slabs=[];U_pending=(k==4);V_pending=(k==1)
 for j in range(Nlocal):
  ta,tb=grid[j],grid[j+1];h=tb-ta
  # Absolute source input/output clock envelopes are independent on first
  # and last slab, all internal knot times are exact rational refinements.
  clockstart=T0 if j==0 else I(ta)
  clockend=T1 if j==Nlocal-1 else I(tb)
  H=clockend-clockstart;assert H.a>0
  timebox=I(clockstart.a,clockend.b)
  mid=[(q.a+q.b)/2 for q in centre]
  radii=[max(q.b-c,c-q.a)+variation[i]+F('1e-8') for i,(q,c) in enumerate(zip(centre,mid))]
  for it in range(80):
   X=[I(c-r,c+r) for c,r in zip(mid,radii)]
   fx,J=s.fJ(X,timebox,mode)
   needed=[max(q.b-c,c-q.a)+variation[i]+H.b*fx[i].mag() for i,(q,c) in enumerate(zip(centre,mid))]
   proposed=[max(r,F(101,100)*v) for r,v in zip(radii,needed)]
   if proposed==radii:break
   radii=proposed
  else:raise AssertionError(('source Picard tube cannot close',j))
  X=[I(c-r,c+r) for c,r in zip(mid,radii)]
  fx,J=s.fJ(X,timebox,mode)
  state=[I(centre[i].a-variation[i],centre[i].b+variation[i]) for i in range(9)]
  pic=[state[i]+I(0,H.b)*fx[i] for i in range(9)]
  assert all(x.within(y) for x,y in zip(pic,X)),('Picard',j)
  # Actual source guard topology, including both one-sided switch slopes.
  gU=s.guard(3,X);gV=s.guard(4,X)
  gUdot=s.guard_slope(3,fx);gVdot=s.guard_slope(4,fx)
  bank=X[4]-F('0.0018');bankdot=fx[4]
  if k==4:
   if U_pending:
    if gU.a>0:U_pending=False
    else:assert gUdot.a>0,('U ON conditional entry slope',j)
   else:assert gU.a>0,('U ON physically positive',j)
   if not V_pending:
    if gV.a<=0:
     V_pending=True;assert gVdot.b<0,('V OFF exit slope',j)
   else:assert gVdot.b<0,('V OFF last interval slope',j)
   assert bank.a>0,('spark ON bank guard',j)
  else:
   assert gU.b<0,('U OFF diode',j)
   if V_pending:
    if gV.a>0:V_pending=False
    else:assert gVdot.a>0,('V ON conditional entry slope',j)
   else:assert gV.a>0,('V ON physically positive',j)
   if not U_pending:
    if bank.a<=0:
     U_pending=True;assert bankdot.b<0,('spark OFF exit slope',j)
   else:assert bankdot.b<0,('spark OFF terminal slope',j)
  tangent,tail,_,L,q=pb.pb8(J,H,N=8)
  P=pb.matmul(tangent,P)
  # Zero-input nominal centre is independently enclosed by a second-order
  # source Taylor formula. Never replace it by a guessed exact centre.
  fx0=s.f(centre,I(ta),mode);sn,co=s.phase(I(ta,tb))
  ft=[I(0) for _ in range(9)]
  ft[5]=-s.PARAM['omega']*s.K*sn;ft[6]=-s.PARAM['omega']*s.K*co
  acc=[ft[i]+sum((J[i][z]*fx[z] for z in range(9)),I(0)) for i in range(9)]
  centre_next=[centre[i]+h*fx0[i]+h*h/F(2)*acc[i] for i in range(9)]
  assert all(v.within(w,strict=False) for v,w in zip(centre_next,X))
  # Positive, componentwise comparison bound for the x0 uncertainty.
  M=[[z.mag() for z in row] for row in J]
  tail_cmp=q*q/F(2)/(1-q/F(3))
  variation_next=[s.up(variation[i]+H.b*sum((M[i][z]*variation[z] for z in range(9)),F(0))+
                  tail_cmp*max(variation)) for i in range(9)]
  # Actual terminal source-clock movement will be separately charged via
  # the explicit dPhi/dt1 = f(t1,Phi) identity below.
  slabs.append(dict(k=j,mode=list(mode),start_time=clockstart.record(),end_time=clockend.record(),
   independent_start_end_time=j in (0,Nlocal-1),
   exact_Picard=True,source_U_guard=gU.record(),source_U_guard_slope=gUdot.record(),
   source_V_guard=gV.record(),source_V_guard_slope=gVdot.record(),
   source_bank_OFF_threshold_signed=bank.record(),source_bank_slope=bankdot.record(),
   physical_V_on_conditional_on_terminal_guard_zero=V_pending,
   source_spark_bank_on=bank.a>0,q=str(q),PB8_tail=str(tail),
   max_input_uncertainty=str(max(variation)),source_centre_end=[v.record() for v in centre_next]))
  centre=centre_next;variation=variation_next
  if j==Nlocal-1:last_tube=X
 # On a true terminal event5 guard gV=0, strict gV'<0 on the suffix and
 # positive gV on the prefix imply no earlier physical V OFF switch.
 assert (not U_pending and V_pending) if k==4 else (U_pending and not V_pending)
 # Full independent event-time derivatives remain from the ordered 9x9 flow.
 centre_with_variation=[I(v.a-variation[i],v.b+variation[i]) for i,v in enumerate(centre)]
 end_f=s.f(last_tube,T1,mode)
 initial_f=s.f(initial,T0,mode)
 partial_start=[-sum((P[i][z]*initial_f[z] for z in range(9)),I(0)) for i in range(9)]
 partial_end=end_f
 # Added explicit endpoint-time uncertainty for output-state enclosure.
 full_end=[centre_with_variation[i]+I(-DT,DT)*end_f[i] for i in range(9)]
 original_next=list(map(F,s.STATES[k+1]))
 terminal_center_included=[v.a<=x<=v.b for v,x in zip(full_end,original_next)]
 target_box_in_output=[v.a<=x-F('0.0001') and x+F('0.0001')<=v.b for v,x in zip(full_end,original_next)]
 output_in_target_box=[x-F('0.0001')<=v.a and v.b<=x+F('0.0001') for v,x in zip(full_end,original_next)]
 assert all(terminal_center_included) and all(target_box_in_output) and not any(output_in_target_box)
 return dict(status=('PASS_SOURCE_J31_ORIGINAL_EVENT1_TO_EVENT2_64_SLAB_CENTRE_RESIDUAL_CONDITIONAL_PHYSICAL_LEG' if k==1 else 'PASS_SOURCE_J31_ORIGINAL_EVENT4_TO_EVENT5_32_SLAB_CENTRE_RESIDUAL_CONDITIONAL_PHYSICAL_LEG'),
  original_mode=list(mode),original_smooth_segment=('event1 V ON to event2 spark OFF' if k==1 else 'event4 U ON to event5 V OFF'),
  complete_smooth_segment_covered=True,nonzero_original_J24_state_radius='1/10000',
  original_J29_full_original_event_start_box_receipt_external=True,
  exact_root_time_brackets_paid_by_J29_external=True,
  independent_original_event_start_end_clock_halfwidth=str(DT),
  original_entry_switch_valid_conditional_on_initial_guard_zero=True,
  original_exit_switch_valid_conditional_on_final_guard_zero=True,
  original_spark_ON_guard_over_all_slabs=(k==4),
  all_strict_picard_slabs=Nlocal,all_PB8_9x9_tangent_slabs=Nlocal,
  source_J24_next_event_centre_in_terminal_enclosure=terminal_center_included,
  source_J24_target_box_geometrically_contained_in_broad_output=target_box_in_output,
  source_output_certified_inside_narrow_J24_target_box=output_in_target_box,
  original_source_DxPhi_interval=[[x.record() for x in row] for row in P],
  original_source_partial_start_clock=[v.record() for v in partial_start],
  original_source_partial_end_clock=[v.record() for v in partial_end],
  final_state_interval=[v.record() for v in full_end],
  original_sixth_state_box_paid=False,full_seven_source_segments_proved=False,
  original_69D_F_DF_complete=False,original_69D_Krawczyk=False,
  periodic_point_proved=False,hardware_metered=False,slabs=slabs)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);ap.add_argument('--segment',type=int,choices=[1,4],default=4);args=ap.parse_args()
 obj=validate(args.segment);args.out.parent.mkdir(parents=True,exist_ok=True)
 args.out.write_text(json.dumps(obj,indent=2)+'\n')
 print(json.dumps({z:obj[z] for z in ('status','all_strict_picard_slabs','all_PB8_9x9_tangent_slabs','original_69D_Krawczyk')},indent=2))
 for d in obj['slabs']:
  if d['k']%4==0 or d['k']==31:print('slab',d['k'],'q',float(F(d['q'])),'v_guard',tuple(float(F(z)) for z in d['source_V_guard']))
if __name__=='__main__':main()
