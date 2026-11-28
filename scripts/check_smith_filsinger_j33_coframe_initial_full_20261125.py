#!/usr/bin/env python3
"""J33 proposal and exact source proof for k0, moving rational frame Lohner form.
Double-precision may suggest Q_j only; exact Fraction verifies source Picard,
frame inverse, Peano-Baker, signed diode/spark guards and full time domain.
"""
import argparse, json, time
from fractions import Fraction as F
from math import sin,cos,sqrt, factorial
from pathlib import Path
from functools import lru_cache
import check_smith_filsinger_j31_native_seven_shortcharts_interval_20261124 as s
import check_smith_filsinger_j32_source_taylor_jets_20261124 as jets
from functools import lru_cache
# The ORIGINAL source functions are unchanged. Cache exact rational phase
# evaluations by interval endpoints: this is memoization, not altered math.
_source_phase=s.phase
@lru_cache(maxsize=60000)
def _phase_by_endpoints(a,b):return _source_phase(s.I(a,b,raw=True))
def _cached_phase(t):
 t=s.I(t);return _phase_by_endpoints(t.a,t.b)
s.phase=_cached_phase
I=s.I

def numpy_candidate(N):
 import numpy as np
 from scipy.integrate import solve_ivp
 p=s.PARAM
 P={k:float(v) for k,v in p.items()};om=P['omega'];kk=3*sqrt(3)/25
 t_end=float(F(s.TIMES[1]));z0=np.array(list(map(float,s.STATES[0])));y0=np.r_[z0,np.eye(9).ravel()]
 def ff(tt,y):
  x=y[:9];i,j,u,v,b,q,r,ih,c=x
  a=-P['R1']*i;bb=u-v-P['R2']*j
  left=-j+P['k']*q+P['kh']*ih;right=j
  f=np.array([(P['L2']*a-P['M']*bb)/2.64,(-P['M']*a+P['L1']*bb)/2.64,
    (1.55*left+right)/1.17,(left+1.4*right)/1.17,
    (-P['Gbleed']*b-ih)/P['Cb'],
    om*r-P['gamma']*q-P['k']*u/2+kk*cos(.3+om*tt),
    -om*q-P['gamma']*r-kk*sin(.3+om*tt),
    (b-c-(P['Rcoil']+P['Rgap'])*ih-P['kh']*u)/P['Lh'],
    (ih-P['Gload']*c)/(P['Ch']*(1+1.5*c*c))])
  J=np.zeros((9,9));A=2.64;B=1.17
  J[0,0]=-P['L2']*P['R1']/A;J[0,1]=P['M']*P['R2']/A;J[0,2]=-P['M']/A;J[0,3]=P['M']/A
  J[1,0]=P['M']*P['R1']/A;J[1,1]=-P['L1']*P['R2']/A;J[1,2]=P['L1']/A;J[1,3]=-P['L1']/A
  J[2,1]=-.55/B;J[2,5]=1.55*P['k']/B;J[2,7]=1.55*P['kh']/B
  J[3,1]=.4/B;J[3,5]=P['k']/B;J[3,7]=P['kh']/B
  J[4,4]=-P['Gbleed']/P['Cb'];J[4,7]=-1/P['Cb']
  J[5,2]=-P['k']/2;J[5,5]=-P['gamma'];J[5,6]=om
  J[6,5]=-om;J[6,6]=-P['gamma']
  J[7,2]=-P['kh']/P['Lh'];J[7,4]=1/P['Lh'];J[7,7]=-(P['Rcoil']+P['Rgap'])/P['Lh'];J[7,8]=-1/P['Lh']
  den=1+1.5*c*c
  J[8,7]=1/(P['Ch']*den)
  J[8,8]=-P['Gload']/(P['Ch']*den)-(ih-P['Gload']*c)*3*c/(P['Ch']*den*den)
  M=y[9:].reshape(9,9)
  return np.r_[f,(J@M).ravel()]
 sol=solve_ivp(ff,(0,t_end),y0,rtol=5e-13,atol=1e-14,method='DOP853',max_step=.0025,dense_output=True)
 assert sol.success
 t=np.linspace(0,t_end,N+1)
 # Frame forward and numerically proposed inverse, independently rationally checked later.
 frames=[]
 for j in range(N+1):
  M=sol.sol(float(t[j]))[9:].reshape((9,9))
  if j==0:M=np.eye(9)
  Minv=np.linalg.inv(M)
  def rat(x):return F(f'{float(x):.12f}')
  frames.append({'Q':[[str(rat(v)) for v in row] for row in M],
                 'B':[[str(rat(v)) for v in row] for row in Minv]})
 return frames

def cand(frames,j):
 return [[F(v) for v in row] for row in frames[j]['Q']],[[F(v) for v in row] for row in frames[j]['B']]

def mm(A,B):
 n=len(A);m=len(B);p=len(B[0]);assert len(A[0])==m
 return [[sum((A[i][k]*B[k][j] for k in range(m)),I(0)) for j in range(p)] for i in range(n)]

def mpoint(A,B):
 return [[sum((A[i][k]*B[k][j] for k in range(len(B))),F(0)) for j in range(len(B[0]))] for i in range(len(A))]

def inverse_box(Q,B):
 # B is a rational proposal. Completely separate actual mathematical proof.
 # Q^{-1}=B(I-E)^{-1} for E=I-QB.
 E=[[F(int(i==j))-sum((Q[i][k]*B[k][j] for k in range(9)),F(0)) for j in range(9)] for i in range(9)]
 err=max(sum(abs(v) for v in row) for row in E);assert err<F(1,10**7),('frame inverse residual large',float(err))
 rad=s.up(err/(1-err))
 return [[I(B[i][j]-rad*sum(abs(v) for v in B[i]),B[i][j]+rad*sum(abs(v) for v in B[i])) for j in range(9)] for i in range(9)],err

def PB(J,h,order=6):
 q=F(h)*max(sum(z.mag() for z in row) for row in J)
 assert q<1,('PB local',float(q))
 K=[[I(int(i==j)) for j in range(9)] for i in range(9)]
 out=[[v for v in row] for row in K]
 hJ=[[z*h for z in row] for row in J]
 for n in range(1,order+1):
  K=mm(K,hJ)
  out=[[out[i][j]+K[i][j]/F(factorial(n)) for j in range(9)] for i in range(9)]
 tail=s.up(q**(order+1)/factorial(order+1)/(1-q/F(order+2)))
 return [[v+I(-tail,tail) for v in row] for row in out],q,tail

def certificate(N=256,stop=None,resume=False,ck='j33_co_checkpoint.json',frames_path='j33_frames.json'):
 t_end=F(s.TIMES[1]);delta=F('0.0001');dt=F('0.000005');lo,hi=map(F,s.BRACKETS[0]);assert t_end-dt<lo<hi<t_end+dt
 mode=s.MODES[0]; assert mode==(0,0,1)
 frames_file=Path(frames_path)
 if not frames_file.exists():
  print('Generating independent numerical rational frame proposals',N,flush=True)
  frames=numpy_candidate(N);frames_file.write_text(json.dumps({'N':N,'frames':frames}))
 else:
  obj=json.loads(frames_file.read_text());assert obj['N']==N;frames=obj['frames']
 import hashlib
 frame_sha=hashlib.sha256(frames_file.read_bytes()).hexdigest()
 point=list(map(F,s.STATES[0]));R=[I(0) for _ in range(9)];D=[[I(0) for _ in range(9)] for i in range(9)]
 signswitch=False;neg=0;positive_slope=0;maxq=F(0);max_eps=F(0);max_D=F(0);max_R=F(0);max_inv=F(0);audit=[];i0=0
 if resume:
  d=json.loads(Path(ck).read_text());assert d['N']==N and d['frames_sha256']==frame_sha
  i0=d['next'];point=list(map(F,d['point']));R=[I(F(a),F(b),raw=True) for a,b in d['R']]
  D=[[I(F(a),F(b),raw=True) for a,b in row] for row in d['D']]
  signswitch=d['signswitch'];neg=d['neg'];positive_slope=d['positive_slope'];maxq=F(d['maxq']);max_eps=F(d['max_eps']);max_D=F(d['max_D']);max_R=F(d['max_R']);max_inv=F(d['max_inv']);audit=d['audit']
 lim=N if stop is None else min(stop,N)
 for j in range(i0,lim):
  tic=time.monotonic();ta=t_end*F(j,N);tb=t_end*F(j+1,N);h=tb-ta;timebox=I(ta,tb)
  Q,B=cand(frames,j);Qnext,Bnext=cand(frames,j+1)
  if j==0:assert Q==[[F(int(i==k)) for k in range(9)] for i in range(9)]
  inv,err=inverse_box(Qnext,Bnext);max_inv=max(max_inv,err)
  # eps=R+(I+D)delta0, with delta0 the *same original nine source coordinates*.
  Qbox=[[I(v) for v in row] for row in Q]
  pert=[R[i]+sum(((I(int(i==k))+D[i][k])*I(-delta,delta) for k in range(9)),I(0)) for i in range(9)]
  ppert=[sum((Qbox[i][k]*pert[k] for k in range(9)),I(0)) for i in range(9)]
  X0=[I(point[i])+ppert[i] for i in range(9)]
  mids=point
  rad=[s.up(max(abs(x.a-point[i]),abs(x.b-point[i]))) for i,x in enumerate(X0)]
  f0=s.f([I(z) for z in point],I(ta),mode)
  tube_r=[s.up(F(101,100)*(rad[i]+F('1e-9')+h*I(f0[i]).mag())) for i in range(9)]
  for it in range(60):
   X=[I(point[i]-tube_r[i],point[i]+tube_r[i]) for i in range(9)]
   fx,J=s.fJ(X,timebox,mode)
   pic=[X0[i]+I(0,h)*fx[i] for i in range(9)]
   if all(pic[i].within(X[i]) for i in range(9)):break
   tube_r=[max(tube_r[i],s.up(F(101,100)*(rad[i]+h*fx[i].mag())+F('1e-11'))) for i in range(9)]
  else: raise AssertionError(('Picard fail',j,float(max(tube_r)),float(max(rad))))
  X=[I(point[i]-tube_r[i],point[i]+tube_r[i]) for i in range(9)];fx,J=s.fJ(X,timebox,mode)
  assert all((X0[i]+I(0,h)*fx[i]).within(X[i]) for i in range(9))
  # signed *source* guard first, then project exact frame uncertainty.
  def guard(which):
   idx=3 if which=='V' else 2;evt=0 if which=='V' else 3
   row=[F(int(k==idx)-int(k==4)) for k in range(9)]
   g0=I(point[idx]-point[4]-F('0.1'))
   w=[sum((I(row[k])*Qbox[k][u] for k in range(9)),I(0)) for u in range(9)]
   gstart=g0+sum((w[u]*pert[u] for u in range(9)),I(0))
   # g'(x) is affine in the source mode; retain signed row/J/Q.
   Jrow=[sum((I(row[k])*J[k][u] for k in range(9)),I(0)) for u in range(9)]
   dr=[sum((Jrow[k]*Qbox[k][u] for k in range(9)),I(0)) for u in range(9)]
   slope=s.I(s.guard_slope(evt,s.f([I(v) for v in point],I(ta),mode)))+sum((dr[u]*pert[u] for u in range(9)),I(0))
   accel=sum((Jrow[k]*fx[k] for k in range(9)),I(0))
   slope=slope+I(0,h)*accel
   return gstart+I(0,h)*slope,slope
  V,Vp=guard('V');U,Up=guard('U')
  assert U.b<0,('U physical OFF guard violated',j,float(U.b))
  assert (X[4]-F('0.0018')).a>0,('spark prematurely OFF',j,float(X[4].a))
  if not signswitch:
   if V.b<0:neg+=1
   else:signswitch=True;assert Vp.a>0,('V-on slope',j,float(Vp.a),float(Vp.b));positive_slope+=1
  else:assert Vp.a>0,('V-on suffix slope',j,float(Vp.a),float(Vp.b));positive_slope+=1
  G,q,tail=PB(J,h,6);maxq=max(maxq,q)
  # Exact rational preconditioned transition, original same-clock frame.
  K=mm(inv,mm(G,Qbox))
  M=[[I(int(i==k))+D[i][k] for k in range(9)] for i in range(9)]
  Mnext=mm(K,M)
  Dnext=[[Mnext[i][k]-I(int(i==k)) for k in range(9)] for i in range(9)]
  pnext,jet=jets.taylor_point_with_remainder(point,ta,h,mode,X,timebox,6)
  assert all(pnext[i].within(X[i],False) for i in range(9))
  newpoint=[s.down((p.a+p.b)/2) for p in pnext]
  local=[pnext[i]-I(newpoint[i]) for i in range(9)]
  Rnext=[sum((K[i][k]*R[k] for k in range(9)),I(0))+sum((inv[i][k]*local[k] for k in range(9)),I(0)) for i in range(9)]
  point=newpoint;D=Dnext;R=Rnext
  epsrad=max(z.mag() for z in pert);max_eps=max(max_eps,epsrad);max_D=max(max_D,max(z.mag() for row in D for z in row));max_R=max(max_R,max(z.mag() for z in R))
  if j%16==15 or j==N-1:
   row=dict(j=j,t=str(tb),q=str(q),eps_radius=str(epsrad),D_radius=str(max(z.mag() for row in D for z in row)),R_radius=str(max(z.mag() for z in R)),V=V.record(),Vp=Vp.record(),U=U.record(),spark=(X[4]-F('0.0018')).record(),max_local_jet_error=str(max(jet)))
   audit.append(row)
   print('J33 C',j,'q',round(float(q),4),'eps',round(float(epsrad),6),'D',round(float(max(z.mag() for row in D for z in row)),5),'V',tuple(round(float(x),4) for x in (V.a,V.b)),'lastsec',round(time.monotonic()-tic,3),flush=True)
 if lim<N:
  data=dict(status='PARTIAL_NOT_FULL_SOURCE_CERTIFICATE',N=N,frames_sha256=frame_sha,next=lim,point=list(map(str,point)),R=[z.record() for z in R],D=[[z.record() for z in row] for row in D],signswitch=signswitch,neg=neg,positive_slope=positive_slope,maxq=str(maxq),max_eps=str(max_eps),max_D=str(max_D),max_R=str(max_R),max_inv=str(max_inv),audit=audit)
  Path(ck).write_text(json.dumps(data)+'\n');return data
 # Endpoint with independently variable event1 clock +/-5e-6.
 Q,B=cand(frames,N);Qbox=[[I(v) for v in row] for row in Q]
 pert=[R[i]+sum(((I(int(i==k))+D[i][k])*I(-delta,delta) for k in range(9)),I(0)) for i in range(9)]
 source_end=[I(point[i])+sum((Qbox[i][k]*pert[k] for k in range(9)),I(0)) for i in range(9)]
 terminal_time=I(t_end-dt,t_end+dt);mids=[(z.a+z.b)/2 for z in source_end]
 bas=s.f(source_end,I(t_end),mode)
 tube_r=[(z.b-z.a)/2+2*dt*I(bas[i]).mag()+F('0.000005') for i,z in enumerate(source_end)]
 for it in range(60):
  XX=[I(m-r,m+r) for m,r in zip(mids,tube_r)];ff,JJ=s.fJ(XX,terminal_time,mode)
  ecandidate=[source_end[i]+I(-dt,dt)*ff[i] for i in range(9)]
  if all(ecandidate[i].within(XX[i]) for i in range(9)):break
  tube_r=[max(tube_r[i],s.up(F(101,100)*((source_end[i].b-source_end[i].a)/2+dt*ff[i].mag()+F('0.000005')))) for i in range(9)]
 else:raise AssertionError('terminal time Picard failed')
 W=[I(m-r,m+r) for m,r in zip(mids,tube_r)];ff,JJ=s.fJ(W,terminal_time,mode)
 assert s.guard_slope(0,ff).a>0 and s.guard(3,W).b<0 and (W[4]-F('0.0018')).a>0
 out=[source_end[i]+I(-dt,dt)*ff[i] for i in range(9)]
 target=list(map(F,s.STATES[1]));membership=[z.a<=v<=z.b for z,v in zip(out,target)]
 assert all(membership),('target numerical event1 centre excluded',membership)
 # The true sensitivity through the original source nominal leg is H=Q(I+D).
 Dnom=mm(Qbox,[[I(int(i==k))+D[i][k] for k in range(9)] for i in range(9)])
 # Bound event1 independently varying clock: I+deltat*J + derivative remainder.
 Linf=max(sum(z.mag() for z in row) for row in JJ);qe=dt*Linf;assert qe<1
 tail=s.up(qe*qe/F(2)/(1-qe/F(3)))
 Btime=[[I(int(i==j))+I(-dt,dt)*JJ[i][j]+I(-tail,tail) for j in range(9)] for i in range(9)]
 Dend=mm(Btime,Dnom)
 return dict(status='PASS_J33_COFRAME_INITIAL_0_TO_EVENT1_CONDITIONAL_SOURCE_NOT_69D',N=N,original_source_mode=[0,0,1],
  fixed_start_clock='0',independent_end_clock=terminal_time.record(),original_J29_event1_root_bracket_inside=True,
  strict_picard_slabs=N,chronological_PB6_slabs=N,signed_V_guard_negative_slabs=neg,positive_V_slope_suffix_slabs=positive_slope,
  U_OFF_entire_time=True,spark_ON_entire_time=True,terminal_V_ON_slope=s.guard_slope(0,ff).record(),
  full_source_terminal_9D=[z.record() for z in out],full_9x9_source_Dx_fixed_clock=[[z.record() for z in row] for row in Dnom],
  full_9x9_source_Dx_independent_event_clock=[[z.record() for z in row] for row in Dend],
  full_event1_clock_partial_9D=[z.record() for z in ff],
  numerical_event1_center_inside=membership,
  max_q=str(maxq),max_coframe_delta=str(max_D),max_reference_R=str(max_R),max_original_input_error_coframe=str(max_eps),
  max_rational_frame_inverse_residual=str(max_inv),rational_frame_proposal_sha256=frame_sha,
  original_event1_zero_guard_root_proved=False,original_69D_Krawczyk=False,periodic_orbit_proved=False,
  full_time_same_clock_frame_verified=True,labelling_source_input_preserved=True,stages=audit)

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--N',type=int,default=256);p.add_argument('--stop',type=int);p.add_argument('--resume',action='store_true');p.add_argument('--ck',default='j33_co_checkpoint.json');p.add_argument('--frames',default='j33_frames.json');p.add_argument('--out',default='j33_co_output.json')
 a=p.parse_args();r=certificate(a.N,a.stop,a.resume,a.ck,a.frames);Path(a.out).write_text(json.dumps(r,indent=2)+'\n');print('STATUS',r['status'])
