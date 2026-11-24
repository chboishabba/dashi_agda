#!/usr/bin/env python3
"""Independent numerical hybrid monodromy + FD adversarial audit. Not interval proof."""
import json,math
import numpy as np
from scipy.integrate import solve_ivp
from scipy.linalg import svdvals
import independent_full_period_numerical_audit as base
P=base.P;tau=base.tau

def J(x,chi):
 i,j,u,v,b,q,r,ih,c= x
 U=bool((u-b-P['Vd'])>0);V=bool((v-b-P['Vd'])>0)
 A=np.zeros((9,9));g=1/P['Rd'];Ld=2.64;Bd=1.17
 A[0,0]=-P['L2']*P['R1']/Ld;A[0,1]=P['M']*P['R2']/Ld;A[0,2]=-P['M']/Ld;A[0,3]=P['M']/Ld
 A[1,0]=P['M']*P['R1']/Ld;A[1,1]=-P['L1']*P['R2']/Ld;A[1,2]=P['L1']/Ld;A[1,3]=-P['L1']/Ld
 A[2,1]=-0.55/Bd;A[2,5]=1.55*P['k']/Bd;A[2,7]=1.55*P['kh']/Bd
 A[3,1]=0.4/Bd;A[3,5]=P['k']/Bd;A[3,7]=P['kh']/Bd
 if U:
  A[2,2]-=1.55*g/Bd;A[2,4]+=1.55*g/Bd
  A[3,2]-=g/Bd;A[3,4]+=g/Bd
  A[4,2]+=g/P['Cb'];A[4,4]-=g/P['Cb']
 if V:
  A[2,3]-=g/Bd;A[2,4]+=g/Bd
  A[3,3]-=1.4*g/Bd;A[3,4]+=1.4*g/Bd
  A[4,3]+=g/P['Cb'];A[4,4]-=g/P['Cb']
 A[4,4]-=P['Gbleed']/P['Cb'];A[4,7]-=int(chi)/P['Cb']
 A[5,2]=-P['k']/2;A[5,5]=-P['gamma_rad']-P['gamma_internal'];A[5,6]=P['omega']
 A[6,5]=-P['omega'];A[6,6]=-P['gamma_rad']-P['gamma_internal']
 A[7,2]=-P['kh']/P['Lh'];A[7,4]=int(chi)/P['Lh'];A[7,7]=-(P['Rcoil']+int(chi)*P['Rgap'])/P['Lh'];A[7,8]=-1/P['Lh']
 den=1+1.5*c*c
 A[8,7]=1/(P['Ch']*den)
 A[8,8]=-P['Gload']/(P['Ch']*den)-(ih-P['Gload']*c)*3*c/(P['Ch']*den*den)
 return A

def hybrid_tangent(x0,rtol=4e-12,atol=1e-13,max_step=0.004):
 t=0.;x=np.asarray(x0,float);T=np.eye(9);chi=True;events=[];salt=[]
 while t<tau-1e-13:
  trigger=P['Voff'] if chi else P['Von']; direction=-1 if chi else 1
  def bank(tt,y):return y[4]-trigger
  bank.terminal=True;bank.direction=direction
  def ode(tt,y):
   z=y[:9];Phi=y[9:].reshape(9,9)
   return np.concatenate([base.f(tt,z,chi), (J(z,chi)@Phi).ravel()])
  y=np.concatenate((x,T.ravel()))
  sol=solve_ivp(ode,(t,tau),y,method='DOP853',rtol=rtol,atol=atol,max_step=max_step,events=bank,dense_output=True)
  if not sol.success:raise RuntimeError(sol.message)
  if len(sol.t_events[0]):
   te=sol.t_events[0][-1];yy=sol.sol(te);x=yy[:9];T=yy[9:].reshape(9,9)
   fpre=np.asarray(base.f(te,x,chi));fpost=np.asarray(base.f(te,x,not chi))
   n=np.zeros(9);n[4]=1
   S=np.eye(9)+np.outer(fpost-fpre,n)/fpre[4]
   det=np.linalg.det(S);expected=fpost[4]/fpre[4]
   assert abs(det-expected)<1e-11
   salt.append(dict(t=float(te),pre_bank_slope=float(fpre[4]),post_bank_slope=float(fpost[4]),det=float(det)))
   T=S@T
   events.append(dict(time=float(te),kind='spark_OFF' if chi else 'spark_ON'))
   chi=not chi;t=te+1e-12
   x=x+np.asarray(base.f(te,x,chi))*1e-12
   # state/time shift already applied via saltation: do NOT also integrate 
   # the tangent with a first-order step. 1e-12 is beneath tolerance.
  else:
   x=sol.y[:9,-1];T=sol.y[9:,-1].reshape(9,9);t=sol.t[-1]
  if len(events)>4:raise RuntimeError('too many spark switches')
 return x,T,salt,chi

def audit():
 x0=base.root0;end,M,salts,on=hybrid_tangent(x0)
 print('tangent endpoint delta',max(abs(end-x0)),'rho',max(abs(np.linalg.eigvals(M))))
 sv=svdvals(np.eye(9)-M);print('sigma_min I-M',sv[-1],'cond',sv[0]/sv[-1]);print('spark salts',salts)
 diffs=[]
 for eps in (3e-4,1e-4,3e-5):
  cols=[];events_pass=True
  for j in range(9):
   pert=np.zeros(9);pert[j]=eps
   yp,cp,ep,_=base.solve_hybrid(x0+pert,max_step=.006)
   ym,cm,em,_=base.solve_hybrid(x0-pert,max_step=.006)
   labels=[v['kind'] for v in ep];labels2=[v['kind'] for v in em]
   if labels!=['V','spark_OFF','spark_ON','U','V','U'] or labels2!=labels:events_pass=False
   cols.append((yp-ym)/(2*eps))
  Mfd=np.column_stack(cols)
  maxerr=float(np.max(np.abs(M-Mfd)))
  rel=float(np.linalg.norm(M-Mfd)/np.linalg.norm(M))
  diffs.append(dict(epsilon=eps,max_abs_error=maxerr,frobenius_relative_error=rel,event_labels_all_match=events_pass))
  print('finite difference',eps,'rel',rel,'max_abs',maxerr,'events_pass',events_pass)
 d=end-x0
 correction=np.linalg.solve(np.eye(9)-M,d)
 xnew=x0+correction
 after,c,labels,_=base.solve_hybrid(xnew,max_step=.006)
 print('corrected defect',max(abs(after-xnew)),'correction size',max(abs(correction)))
 result=dict(scope='nonrigorous_DOP853_hybrid_variational_ODE_and_event_central_differences',initial_return_defect_inf=float(max(abs(d))),corrected_return_defect_inf=float(max(abs(after-xnew))),correction_inf=float(max(abs(correction))),corrected_x=xnew.tolist(),M=M.tolist(),rho=float(max(abs(np.linalg.eigvals(M)))),sigma_min_IminusM=float(sv[-1]),condition_IminusM=float(sv[0]/sv[-1]),sparks=salts,checks=diffs,corrected_event_labels=[e['kind'] for e in labels],corrected_event_times=[e['time'] for e in labels],source_pinned_interval_certificate=False,nonzero_ball_derivative_proved=False,banach_fixed_point_proved=False,physical_hardware_verified=False)
 path=__import__('pathlib').Path(__file__).resolve().parents[1]/'Artifacts/smith-filsinger/full_period_monodromy_diagnostic_20261124.json'
 path.write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':audit()
