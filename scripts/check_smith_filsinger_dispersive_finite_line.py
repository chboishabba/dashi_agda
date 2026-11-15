#!/usr/bin/env python3
"""Finite charged source -> nonlinear distributed line -> useful receiver.
NORMALISED coefficients; NOT a fitted Filsinger / ionosphere device.
Causal local transmission-line dynamics, nonlinear polarisation memory,
spatially restricted modulated susceptibility, signed reservoir/control
work, reciprocal source depletion and receiving load.
"""
from dataclasses import dataclass
import numpy as np
from scipy.integrate import solve_ivp
@dataclass(frozen=True)
class Params:
 N:int=9
 C:float=.85
 L:float=.9
 Csrc:float=15.
 Gfeed:float=.75
 Rline:float=.015
 Gline:float=.006
 Rload:float=1.6
 chi0:float=.25
 beta:float=.45
 eta:float=.35
 mod_depth:float=.22
 modfreq:float=2.8
 source_initial_voltage:float=2.
 natural_recharge_current:float=.01
 drive_amplitude:float=.035
 drive_omega:float=2.9
 mod_until:float=11.
 duration:float=14.

def modulation(t,phase,p):
 if t>=p.mod_until:return 0.,0.
 theta=np.pi*t/p.mod_until
 w=np.sin(theta)**2
 dw=np.pi/p.mod_until*np.sin(2*theta)
 angle=p.modfreq*t+phase
 return p.mod_depth*w*np.cos(angle),p.mod_depth*(dw*np.cos(angle)-w*p.modfreq*np.sin(angle))

def run(phase=0.,p=Params(),with_source=True,with_modulation=True):
 N=p.N;center=N//2; selected=np.array([center-1,center,center+1])
 V=slice(0,N);I=slice(N,2*N-1);P=slice(2*N-1,3*N-1);ISRC=3*N-1
 state=np.zeros(3*N+7)
 state[ISRC]=p.source_initial_voltage if with_source else 0.
 def physics(t,z):
  v=z[V];i=z[I];pol=z[P];vs=z[ISRC]
  m,dm=modulation(t,phase,p) if with_modulation else (0.,0.)
  chi=np.full(N,p.chi0);dchi=np.zeros(N)
  chi[selected]=p.chi0*(1+m)
  dchi[selected]=p.chi0*dm
  pdot=(v-pol/chi-p.beta*pol**3)/p.eta
  Is=p.Gfeed*(vs-v[0])
  incoming=np.zeros(N);outgoing=np.zeros(N)
  incoming[0]+=Is;incoming[1:]+=i
  outgoing[:-1]+=i;outgoing[-1]+=v[-1]/p.Rload
  Id=p.drive_amplitude*np.cos(p.drive_omega*t) if t<p.mod_until else 0.
  incoming[center]+=Id
  vdot=(incoming-outgoing-p.Gline*v-pdot)/p.C
  idot=(v[:-1]-v[1:]-p.Rline*i)/p.L
  recharge=p.natural_recharge_current if with_source else 0.
  dsrc=(recharge-Is)/p.Csrc
  wdriver=Id*v[center]
  wrecharge=recharge*vs
  wmaterial=-.5*np.sum(pol**2*dchi/chi**2)
  wload=v[-1]**2/p.Rload
  wloss=p.Gline*np.dot(v,v)+p.Rline*np.dot(i,i)+p.eta*np.dot(pdot,pdot)
  wfeed=Is**2/p.Gfeed
  wtransfer=Is*v[0]
  return (vdot,idot,pdot,dsrc),(wdriver,wrecharge,wmaterial,wload,wloss,wfeed,wtransfer),chi
 def f(t,z):
  q,w,_=physics(t,z)
  return np.r_[*q,w]
 def U(t,z):
  v=z[V];i=z[I];pol=z[P];vs=z[ISRC]
  chi=physics(t,z)[2]
  return .5*(p.C*np.dot(v,v)+p.L*np.dot(i,i)+p.Csrc*vs*vs)+np.sum(pol**2/(2*chi)+p.beta*pol**4/4)
 sol=solve_ivp(f,(0,p.duration),state,rtol=1e-9,atol=1e-11,max_step=.011,method='DOP853')
 if not sol.success:raise RuntimeError(sol.message)
 last=sol.y[:,-1]; wd,wn,wm,wl,loss,feed,transfer=map(float,last[3*N:])
 source0=.5*p.Csrc*state[ISRC]**2
 source1=.5*p.Csrc*last[ISRC]**2
 return dict(phase=float(phase),has_source=bool(with_source),
  source_initial=float(source0),source_final=float(source1),
  source_recharge=wn,driver_work=wd,material_modulation_work=wm,
  useful_load=wl,distributed_loss=loss,source_feed_loss=feed,
  natural_source_to_line=transfer,
  total_energy_initial=float(U(0,state)),
  total_energy_final=float(U(p.duration,last)),
  total_balance_residual=float(U(p.duration,last)-U(0,state)-wd-wn-wm+wl+loss+feed),
  donor_balance_residual=float(transfer-(source0+wn-source1-feed)),
  node_count=N,nfev=sol.nfev)

def check():
 p=Params(); allrows=[]
 for phase in np.linspace(0,2*np.pi,8,endpoint=False):
  for source in (True,False):
   row=run(float(phase),p,source)
   assert abs(row['total_balance_residual'])<1e-8,row
   assert abs(row['donor_balance_residual'])<1e-8,row
   if source:
    assert row['source_initial']>row['source_final']
   else:
    assert row['source_initial']==0 and row['source_recharge']==0
   allrows.append(row)
 from dataclasses import replace
 dead=replace(p,source_initial_voltage=0.,natural_recharge_current=0.,drive_amplitude=0.)
 assert run(1.3,dead)['useful_load']<1e-14
 yes=[q['useful_load'] for q in allrows if q['has_source']]
 no=[q['useful_load'] for q in allrows if not q['has_source']]
 assert np.mean(yes)>1000*np.mean(no)
 assert 0<np.ptp(yes)<.01 # phase sensitivity modest in THIS model
 return allrows

if __name__=='__main__':
 import json
 print(json.dumps(check(),indent=2))
 print('PASS 16 nonlinear distributed source-control trajectories and all work ports')
