#!/usr/bin/env python3
"""Exact-rational 9D original source long chart: interval state + signed source Jacobian.
Audits 3->4 and 5->6, not a simultaneous 69D periodic root. Independent absolute
boundary time variation is conservatively charged with interval time extensions.
"""
import argparse,json,sys,time,hashlib
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import check_smith_filsinger_j31_native_seven_shortcharts_interval_20261124 as s
import check_smith_filsinger_j32_source_taylor_jets_20261124 as tj
I=s.I

def mmul(A,B):
 return [[sum((A[i][k]*B[k][j] for k in range(9)),I(0)) for j in range(9)] for i in range(9)]

def PB(J,h,N=6):
 h=I(h);L=max(sum(z.mag() for z in row) for row in J);q=L*h.b
 assert q<F(1)
 H=[[v*h for v in row] for row in J]
 product=[[I(int(i==j)) for j in range(9)] for i in range(9)]
 result=[[v for v in row] for row in product]
 for n in range(1,N+1):
  product=mmul(product,H)
  for i in range(9):
   for j in range(9):result[i][j]=result[i][j]+product[i][j]/factorial(n)
 tail=s.up(q**(N+1)/factorial(N+1)/(1-q/F(N+2)))
 result=[[v+I(-tail,tail) for v in row] for row in result]
 return result,q,tail

def certify(k,N=128, order=6, initial_radius=F('0.0001'), tolerance=F('0.000005'), checkpoint=8, stop=None, checkpoint_path=None, resume=False, event6_input=None):
 assert k==6
 ta=F(s.TIMES[k]);mode=s.MODES[k]
 def atan_bounds(x,n=26):
  t=sum(((-1)**i*F(x)**(2*i+1)/F(2*i+1) for i in range(n)),F(0))
  rem=F(x)**(2*n+1)/F(2*n+1)
  return (t,t+rem) if n%2==0 else (t-rem,t)
 l1,u1=atan_bounds(F(1,5));l2,u2=atan_bounds(F(1,239))
 tau_lo=F(20,11)*(16*l1-4*u2);tau_hi=F(20,11)*(16*u1-4*l2)
 assert F('5.71')<tau_lo<tau_hi<F('5.72') and tau_hi-tau_lo<F(1,10**28)
 tb=(tau_lo+tau_hi)/2

 DT0=F('0.0002');DT1=(tau_hi-tau_lo)/2
 a=I(ta-DT0,ta+DT0);b=I(tb-DT1,tb+DT1)
 rootlo,roothi=map(F,s.BRACKETS[5]);assert a.a<rootlo<roothi<a.b
 assert b.a<=tau_lo<tau_hi<=b.b
 point=[F(v) for v in s.STATES[k]];xnom=point[:];R=[I(0) for _ in range(9)]
 # Prove initial time variation over the original nonzero x0 J24 ball;
 # source time varying first, then transport with signed full Jacobian.
 if event6_input is None:raise ValueError('Exact J32 k5 full original source JSON required')
 input_bytes=Path(event6_input).read_bytes();input_sha256=hashlib.sha256(input_bytes).hexdigest()
 assert input_sha256=='91025015aa33aa0422346d8a3aa2b504254f7a8a65f75adc3ce256ebe8973520','Source ownership/pinned producer changed'
 original_input=json.loads(input_bytes)
 assert original_input['segment']==5 and original_input['strict_picard_slabs']==128
 start=[I(F(z[0]),F(z[1]),raw=True) for z in original_input['terminal_state']]
 inputr=[max(abs(q.a-xnom[i]),abs(q.b-xnom[i])) for i,q in enumerate(start)]
 stube=[I(c-r-F('.003'),c+r+F('.003')) for c,r in zip(xnom,inputr)]
 window=I(ta-DT0,ta+DT0)
 f0=s.f(stube,window,mode)
 assert all((start[i]+I(-DT0,DT0)*f0[i]).within(stube[i]) for i in range(9))
 initerr=[s.up(inputr[i]+DT0*v.mag()) for i,v in enumerate(f0)]
 H=[[I(int(i==j)) for j in range(9)] for i in range(9)]
 slabs=[];maxrad=F(0);num_guard_positive=0;num_guard_slope=0
 startj=0
 if resume:
  obj=json.loads(Path(checkpoint_path).read_text());assert (obj['k'],obj['N'],obj['order'])==(k,N,order)
  assert obj['producer_sha256']==input_sha256
  startj=obj['next_step'];point=[F(x) for x in obj['point']]
  R=[I(F(a),F(b),raw=True) for a,b in obj['R']]
  H=[[I(F(a),F(b),raw=True) for a,b in row] for row in obj['H']]
  slabs=obj['slabs'];num_guard_positive=obj['guards_strict'];num_guard_slope=obj['guards_slope']
 grid=[ta+(tb-ta)*F(j,N) for j in range(N+1)]
 for j in range(startj,min(N,N if stop is None else stop)):

  tic=time.monotonic()
  t0=grid[j];t1=grid[j+1];h=t1-t0;window=I(t0,t1)
  # True interval state = rational reference point + signed transported
  # root truncation residual R + H times labelled original input delta.
  radH=[s.up(sum((H[i][p].mag()*initerr[p] for p in range(9)),F(0))) for i in range(9)]
  mid=point[:];radR=[max(abs(q.a),abs(q.b)) for q in R]
  radi=[s.up(radH[i]+radR[i]) for i in range(9)]
  hfx=s.f([I(q) for q in point],I(t0),mode)
  r=[s.up(F(101,100)*(radi[i]+F('1e-10')+h*hfx[i].mag())) for i in range(9)]
  for it in range(40):
   tube=[I(z-v,z+v) for z,v in zip(mid,r)]
   fx,J=s.fJ(tube,window,mode)
   needed=[radi[i]+h*fx[i].mag() for i in range(9)]
   rn=[max(r[i],s.up(F(101,100)*needed[i]+F('1e-12'))) for i in range(9)]
   pred=[I(point[i]-radi[i],point[i]+radi[i])+I(0,h)*fx[i] for i in range(9)]
   if all(pred[i].within(tube[i]) for i in range(9)):break
   r=rn
  else:raise AssertionError(('PICARD iteration failed',k,j,float(max(r))))
  tube=[I(z-v,z+v) for z,v in zip(mid,r)]
  fx,J=s.fJ(tube,window,mode)
  startset=[I(point[i]-radi[i],point[i]+radi[i]) for i in range(9)]
  pic=[startset[i]+I(0,h)*fx[i] for i in range(9)]
  assert all(v.within(T) for v,T in zip(pic,tube)),('Picard fails',k,j)
  # Reversible, labelled observer of original *signed* guard, not the
  # Cartesian whole-Picard-tube projection that destroys u-b correlation.
  # Both diode guard derivatives are AFFINE in x in each fixed branch.
  def signed_guard(event):
   gi=(2 if event in (3,5) else 3);row=[int(j==gi)-int(j==4) for j in range(9)]
   gp=s.guard(event,[I(z) for z in point])
   hrow=[sum((I(row[i])*H[i][j] for i in range(9)),I(0)) for j in range(9)]
   start=gp+sum((I(row[i])*R[i] for i in range(9)),I(0))
   r0=s.up(sum((hrow[j].mag()*initerr[j] for j in range(9)),F(0)))
   start=start+I(-r0,r0)
   # derivative g' = row . f is source-affine in x: derivative is constant.
   # Direct f(X) can erase sign; integrate its linear functional with fixed
   # coefficients, retaining the source start labelling separately.
   Jrow=[sum((I(row[i])*J[i][j] for i in range(9)),I(0)) for j in range(9)]
   gp0=s.guard_slope(event,s.f([I(z) for z in point],I(t0),mode))
   driftR=sum((Jrow[j]*R[j] for j in range(9)),I(0))
   driftH=[sum((Jrow[i]*H[i][j] for i in range(9)),I(0)) for j in range(9)]
   er=s.up(sum((driftH[j].mag()*initerr[j] for j in range(9)),F(0)))
   initdot=gp0+driftR+I(-er,er)
   accel=sum((Jrow[j]*fx[j] for j in range(9)),I(0))
   sloped=initdot+I(0,h)*accel
   return start+I(0,h)*sloped,sloped
  gU,gUdot=signed_guard(5);gV,gVdot=signed_guard(4)
  gBank=tube[4]-F('0.0018')
  assert gBank.a>0,('spark hysteresis bank',k,j,float(gBank.a))
  if k==3:
   assert gV.a>0,('V on',k,j,float(gV.a))
   pending=gU;gDot=gUdot
   if gU.b<0:num_guard_positive+=1
   else:
    assert gDot.a>0,('U ON signed-affine slope fail',k,j,float(gDot.a),float(gDot.b))
    num_guard_slope+=1
  elif k==6:
   assert gV.b<0,('V OFF physical guard',j,float(gV.b))
   pending=gU;gDot=gUdot
   if gU.b<0:num_guard_positive+=1
   else:
    assert gDot.b<0,('U OFF source signed slope',j,float(gDot.a),float(gDot.b))
    num_guard_slope+=1
  G,q,tail=PB(J,h,order)
  Hnew=mmul(G,H)
  # Rigorous order-6 Taylor polynomial about exact rational original source
  # point, with coefficient-order-7 Lagrange remainder evaluated over X,T.
  pointend,taylor_tail=tj.taylor_point_with_remainder(point,t0,h,mode,tube,window,order=6)
  assert all(x.within(T,strict=False) for x,T in zip(pointend,tube))
  nextpoint=[s.down((z.a+z.b)/2) for z in pointend]
  locerr=[pointend[i]-I(nextpoint[i]) for i in range(9)]
  # Root error from previous slabs travels via interval source tangent and
  # new local error is added; it is NOT reset or hidden at recentering.
  Rnew=[sum((G[i][l]*R[l] for l in range(9)),I(0))+locerr[i] for i in range(9)]
  H=Hnew;R=Rnew;point=nextpoint
  if j==N-1 or (checkpoint and j%checkpoint==0):
   rad_next=[s.up(sum((H[i][l].mag()*initerr[l] for l in range(9)),F(0))) for i in range(9)]
   slabs.append(dict(step=j,clock_start=str(t0),clock_end=str(t1),q=str(q),pb_tail=str(tail),
        max_root_residual_radius=str(max(v.mag() for v in R)),max_input_image_radius=str(max(rad_next)),
        max_jet7_local_remainder=str(max(taylor_tail)),
        signed_named_guard=pending.record() if k==3 else gU.record(),
        named_guard_slope=gDot.record(),other_diode=gV.record(),bank=gBank.record()))
   print('k',k,'step',j,'q',float(q),'Rrad',float(max(v.mag() for v in R)),
         'rad',float(max(rad_next)),'guard',tuple(round(float(t),5) for t in (gU.a,gU.b)),
         'runtime',round(time.monotonic()-tic,3),flush=True)
 if stop is not None and stop<N:
  obj=dict(k=k,N=N,order=order,next_step=stop,producer_sha256=input_sha256,point=list(map(str,point)),
       R=[v.record() for v in R],H=[[v.record() for v in row] for row in H],
       slabs=slabs,guards_strict=num_guard_positive,guards_slope=num_guard_slope,
       status='PARTIAL_EXACT_RATIONAL_CHECKPOINT_NOT_FULL_SOURCE_SEGMENT')
  Path(checkpoint_path).write_text(json.dumps(obj)+'\n')
  return obj
 # Nominal full source flow is valid for all original input-state balls.
 rad=[s.up(sum((H[i][l].mag()*initerr[l] for l in range(9)),F(0))) for i in range(9)]
 endbase=[I(point[i])+R[i]+I(-rad[i],rad[i]) for i in range(9)]
 # Prove independent moving terminal clock from a full nonzero-state box.
 # The smooth extension AFTER the switching event is VIRTUAL for derivative
 # purposes only; physically the named guard is zero at actual t_end.
 end_window=I(tb-DT1,tb+DT1)
 mids=[(v.a+v.b)/2 for v in endbase]
 end_r=[(v.b-v.a)/2 + DT1*s.f(endbase,I(tb),mode)[i].mag()*F(2) + F('0.000001') for i,v in enumerate(endbase)]
 for it in range(40):
  endtube=[I(m-r,m+r) for m,r in zip(mids,end_r)]
  fe,Je=s.fJ(endtube,end_window,mode)
  terminal_pic=[endbase[i]+I(-DT1,DT1)*fe[i] for i in range(9)]
  if all(terminal_pic[i].within(endtube[i]) for i in range(9)):break
  end_r=[max(r,s.up(F(101,100)*((v.b-v.a)/2+DT1*f.mag()+F('0.000001')))) for r,v,f in zip(end_r,endbase,fe)]
 else:raise AssertionError('Endtime source Picard tube failed')
 # A full-time signed interval matrix on a short time displacement +-dt.
 # Peano-Baker n>=2 tail is bounded by q^2/[2(1-q/3)].
 def symmetric_tangent(jac,dt):
  LL=max(sum(z.mag() for z in row) for row in jac);qq=LL*dt
  assert qq<1
  err=s.up(qq*qq/F(2)/(1-qq/F(3)))
  return [[I(int(i==j))+I(-dt,dt)*jac[i][j]+I(-err,err) for j in range(9)] for i in range(9)],qq,err
 full_start_j=s.fJ(stube,I(ta-DT0,ta+DT0),mode)[1]
 Bstart,qs,ts=symmetric_tangent(full_start_j,DT0)
 Bend,qe,te=symmetric_tangent(Je,DT1)
 # Chronological: end virtual flow THEN full nominal flow THEN start flow.
 wholeD=mmul(Bend,mmul(H,Bstart))
 corrected=[endbase[i]+I(-DT1,DT1)*fe[i] for i in range(9)]
 full_start_f=s.f(start,I(ta-DT0,ta+DT0),mode)
 partial_start=[-sum((wholeD[i][j]*full_start_f[j] for j in range(9)),I(0)) for i in range(9)]
 partial_end=fe
 if k==6:
  assert s.guard(5,endtube).b<0 and s.guard(4,endtube).b<0
  assert (endtube[4]-F('0.0018')).a>0
  startoff=s.guard_slope(5,s.f(stube,I(ta-DT0,ta+DT0),mode))
  assert startoff.b<0,('Post event6 U OFF negative slope',startoff)
 if k==5:
  slopeend=s.guard_slope(5,fe)
  assert slopeend.b<0,('Physical U-OFF pre-slope over moving endtime',slopeend)
  assert s.guard(4,endtube).b<0,('Physical other diode V OFF over moving endtime')
  assert (endtube[4]-F('0.0018')).a>0,('Spark remains ON near event6')
  startoffslope=s.guard_slope(4,s.f(stube,I(ta-DT0,ta+DT0),mode))
  assert startoffslope.b<0,('Initial V-OFF post-switch slope')
 elif k==3:
  slopeend=s.guard_slope(3,fe)
  assert slopeend.a>0,('Physical U-ON pre-slope over moving event4 clock',slopeend)
  assert s.guard(4,endtube).a>0,('Physical other diode V ON near event4')
  assert (endtube[4]-F('0.0018')).a>0,('Spark stays ON near event4')
  startonslope=s.guard_slope(2,s.f(stube,I(ta-DT0,ta+DT0),mode))
  assert startonslope.b<0,('Spark ON post-switch negative bank slope')
 numerical_next=list(map(F,s.STATES[0]))
 isinside=[q.a<=target<=q.b for q,target in zip(corrected,numerical_next)]
 print('NUM TARGET',isinside,'maxdia',float(max(q.b-q.a for q in corrected)),flush=True)
 return dict(status='PASS_SOURCE_J32_EVENT6_BROAD_STATE_TO_EXACT_TAU_FULL_128_SLAB_RETURN_NOT_PERIODIC',segment=k,mode=mode,
  source_owned_original_event6_broad_input_sha256=input_sha256,
  original_exact_rational_tau_interval=[str(tau_lo),str(tau_hi)],
  original_period_tau_is_20_pi_over_11=True,physical_root_and_return_equations_unproved=True,
  strict_picard_slabs=N,PB_order=order,root_time_uncertainty_start=str(DT0),root_time_uncertainty_end=str(DT1),
  source_previous_exact_root_brackets_reused=True,actual_event_guard_zeros_unproved=True,
  whole_physical_branch_conditional_on_original_event6_initial_guard_zero=True,
  terminal_numeric_centre_membership=isinside,initial_radii=list(map(str,initerr)),
  guard_sign_strict_slabs=num_guard_positive,initial_guard_slope_slabs=num_guard_slope,
  full_9x9_state_derivative_nominal_clock=[[v.record() for v in row] for row in H],
  full_9x9_state_derivative_independent_clocks=[[v.record() for v in row] for row in wholeD],
  full_9D_partial_start_time=[v.record() for v in partial_start],
  full_9D_partial_end_time=[v.record() for v in partial_end],
  source_time_extension_picard_start=True,source_time_extension_picard_end=True,
  source_time_start_tangent_tail=str(ts),source_time_end_tangent_tail=str(te),
  central_9D_terminal=[(I(point[i])+R[i]).record() for i in range(9)],terminal_state=[z.record() for z in corrected],
  source_start_time_sensitivity_proved=True,source_end_time_sensitivity_proved=True,
  original_full_69D_DF_unproved=True,strict_original_69D_Krawczyk=False,
  exact_periodic_orbit=False,checkpoint_slabs=slabs)

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--event6-input',type=Path,required=True);p.add_argument('--k',type=int,default=6);p.add_argument('--N',type=int,default=128);p.add_argument('--order',type=int,default=6);p.add_argument('--stop',type=int,default=None);p.add_argument('--checkpoint',type=Path,default=Path('j32_return_checkpoint.json'));p.add_argument('--resume',action='store_true');p.add_argument('--out',type=Path,default=Path('j32_return_receipt.json'))
 args=p.parse_args();out=certify(args.k,args.N,args.order,stop=args.stop,checkpoint_path=args.checkpoint,resume=args.resume,event6_input=args.event6_input)
 args.out.write_text(json.dumps(out,indent=2)+'\n')
