#!/usr/bin/env python3
"""Independent source-equation numerical six-event and Poincare diagnostic.
Not a validated interval proof; never promotes J24 boxes or a fixed point.
"""
import json, math
from pathlib import Path
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import root

tau=20*math.pi/11
PARAM={k:float(v) for k,v in dict(L1='2',L2='1.5',M='.6',R1='.35',R2='.28',C='1',Cu='.4',Cv='.55',Cb='.65',Rd='.12',Vd='.1',Gbleed='.018',Von='.006',Voff='.0018',omega='1.1',gamma_rad='.015',gamma_internal='.0002',k='.35',source_amp='1.2',Lh='.15',Ch='.12',alpha='.5',Rgap='.09',Rcoil='.05',Gload='.52',kh='2').items()}
P=PARAM
root0=np.array(list(map(float,['-0.04585851023046709','0.0967120405698972','1.9865816276887802','1.1890650910077614','2.3839347955003958','5.502919318568432','-5.781120275385947','-0.7451738522543331','-1.5585226674954609'])))

def f(t,x,chi):
 i,j,u,v,b,q,r,ih,c= x
 ju=max(0,(u-b-P['Vd'])/P['Rd']); jv=max(0,(v-b-P['Vd'])/P['Rd'])
 a=-P['R1']*i;bb=u-v-P['R2']*j
 left=-j-ju+P['k']*q+P['kh']*ih;right=j-jv
 di=(P['L2']*a-P['M']*bb)/2.64; dj=(-P['M']*a+P['L1']*bb)/2.64
 du=(1.55*left+right)/1.17; dv=(left+1.4*right)/1.17
 db=(ju+jv-P['Gbleed']*b-int(chi)*ih)/P['Cb']
 gam=P['gamma_rad']+P['gamma_internal']
 dq=P['omega']*r-gam*q-P['k']*u/2+math.sqrt(.03)*P['source_amp']*math.cos(.3+P['omega']*t)
 dr=-P['omega']*q-gam*r-math.sqrt(.03)*P['source_amp']*math.sin(.3+P['omega']*t)
 dih=(int(chi)*b-c-(P['Rcoil']+int(chi)*P['Rgap'])*ih-P['kh']*u)/P['Lh']
 dc=(ih-P['Gload']*c)/(P['Ch']*(1+1.5*c*c))
 return [di,dj,du,dv,db,dq,dr,dih,dc]

def solve_hybrid(x0,t0=0.,t1=tau,chi0=True,rtol=8e-12,atol=2e-13,max_step=.007):
 t=float(t0);x=np.array(x0,dtype=float);chi=chi0;hist=[];segments=[]
 while t<t1-2e-13:
  trigger=P['Voff'] if chi else P['Von']
  direction=-1 if chi else 1
  def bank(t,z):return z[4]-trigger
  bank.terminal=True;bank.direction=direction
  def U(t,z):return z[2]-z[4]-P['Vd']
  U.terminal=False;U.direction=0
  def V(t,z):return z[3]-z[4]-P['Vd']
  V.terminal=False;V.direction=0
  sol=solve_ivp(lambda tt,xx:f(tt,xx,chi),(t,t1),x,method='DOP853',rtol=rtol,atol=atol,max_step=max_step,events=(bank,U,V),dense_output=True)
  if not sol.success:raise RuntimeError(sol.message)
  for kind,ev in [('U',sol.t_events[1]),('V',sol.t_events[2])]:
   for at in ev:
    if at>t+1e-9:hist.append(dict(time=float(at),kind=kind,post_active=bool(kind=='U' and (sol.sol(at+min(1e-8,sol.t[-1]-at))[2]-sol.sol(at+min(1e-8,sol.t[-1]-at))[4]-P['Vd'])>0) if kind=='U' else bool((sol.sol(at+min(1e-8,sol.t[-1]-at))[3]-sol.sol(at+min(1e-8,sol.t[-1]-at))[4]-P['Vd'])>0),state=sol.sol(at).tolist()))
  if len(sol.t_events[0]):
   at=float(sol.t_events[0][-1]);x=sol.sol(at);hist.append(dict(time=at,kind='spark_OFF' if chi else 'spark_ON',state=x.tolist()));chi=not chi;t=at+1e-12;x=np.asarray(x)+np.asarray(f(at,np.asarray(x),chi))*1e-12
  else: t=sol.t[-1];x=sol.y[:,-1]
  segments.append((len(sol.t),chi,t))
  if len(segments)>50:raise RuntimeError('too many spark events')
 return x,chi,sorted(hist,key=lambda z:z['time']),segments

def main():
 path=Path(__file__).resolve().parents[1]/'Artifacts/smith-filsinger/j28b_signed_75_step_exact_checkpoint_20261123.json'
 ck=json.loads(path.read_text());xp=np.array([float(eval_fraction(v)) for v in ck['root']]);delta=np.array([float(eval_fraction(v)) for v in ck['delta']]);
 tail,chi,eh,_=solve_hybrid(xp,4.26534095,tau,True)
 physicalEvents=[a for a in eh if a['kind'] in ('U','V')]
 # Remove U root almost coincident with initial 4.265? no, inspect all.
 full,mode,events,segments=solve_hybrid(root0)
 enddefect=(full-root0)
 centre_t=[3.38936700888198,3.49129272118508,3.51534047913749,4.27548902321254,4.3238379476284,4.9287514068571]
 klist=['V','spark_OFF','spark_ON','U','V','U']
 source=[[0.12348312106665,-0.33068865436942,-0.61498992005122,0.12478194459184,0.02478194459184,-1.26821663487563,8.05084491010875,0.29147231465058,1.36414548330839],
 [0.13523459842601,-0.37755904088316,-0.57949133558498,0.11808477566022,0.0018,-0.35976396951008,8.14678092946336,0.19549754734332,1.25957158565016],
 [0.13777688770661,-0.38794832888392,-0.56840423619862,0.11753667895618,0.006,-0.14428501896863,8.15470656353592,0.17836730293335,1.23181233103631],
 [0.1575089933189,-0.52392044646492,0.40607309976167,0.42213199004971,0.30607309976167,5.94776080307441,5.642624741628,-0.40580972792692,-0.2565046667794],
 [0.15431688550553,-0.51767847907243,0.4858280655798,0.45489512322921,0.35489512322921,6.23432987041079,5.32411883721043,-0.46942327080398,-0.35480689258185],
 [0.08472814436407,-0.32935984299057,1.33978173940005,0.83433116172484,1.23978173940005,8.13119780949747,0.42908731743842,-0.98106986849663,-1.1666415376269]]
 def describe(evs):
  return [dict(kind=a['kind'],time=a['time'],state=a['state']) for a in evs]
 print('full six candidate events',[(a['kind'],round(a['time'],10)) for a in events]);print('tail three candidate events',[(a['kind'],round(a['time'],10)) for a in eh]);print('terminal defect',np.linalg.norm(enddefect,np.inf),'mode',mode);print('checkpoint max delta',max(delta))
 if len(events)==6 and [x['kind'] for x in events]==klist:
  for idx,e in enumerate(events):print('event',idx+1,'dt',e['time']-centre_t[idx],'dstate',max(abs(np.array(e['state'])-source[idx])))
 else:print('WARN: NOT SIX EVENT MATCH')
 out={'scope':'nonrigorous_independent_scipy_diagnostic_only','tau':tau,'root0':root0.tolist(), 'end':full.tolist(),'terminal_defect':enddefect.tolist(), 'terminal_defect_inf':float(np.linalg.norm(enddefect,np.inf)), 'mode_final_on':bool(mode), 'events':describe(events),'from_J28B_stage75':{'initial_center':xp.tolist(),'initial_delta_inf':float(max(delta)),'events':describe(eh),'terminal':tail.tolist()},'J24_centres':source,'J24_numerical_event_times':centre_t,'valid_interval_certificate':False,'periodic_orbit_proved':False,'original_hardware_verified':False}
 (Path(__file__).resolve().parents[1]/'Artifacts/smith-filsinger/full_period_numerical_diagnostic_20261124.json').write_text(json.dumps(out,indent=2)+'\n')

def eval_fraction(s):
 from fractions import Fraction
 return Fraction(s)
if __name__=='__main__':main()
