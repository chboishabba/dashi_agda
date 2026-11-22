#!/usr/bin/env python3
"""J12 conditional restored-cycle S3/S5 source/driver ledger.
Synthetic dimensionless case; never an authenticated Filsinger circuit.
"""
import json,math,numpy as np
from scipy.integrate import solve_ivp
P=dict(L1=2.,L2=1.5,M=.6,R1=.35,R2=.28,C=1.,Cu=.4,Cv=.55,Cb=.65,Rd=.12,Vd=.1,Gbleed=.018,Gspark=1.1,Von=.22,Voff=.075,omega=1.1,gamma_rad=.085,gamma_internal=.04,k=.15,source_amp=.10)
T=20*math.pi
def advance(p,inc,phi,state,active,t0):
 L=np.array([[p['L1'],p['M']],[p['M'],p['L2']]]);A=np.array([[p['C']+p['Cu'],-p['C']],[-p['C'],p['C']+p['Cv']]])
 assert min(np.linalg.eigvalsh(L))>0 and min(np.linalg.eigvalsh(A))>0
 li=np.linalg.inv(L);ai=np.linalg.inv(A);rad=np.sqrt(2*p['gamma_rad'])
 def energy(x):
  i,j,u,v,b,q,z=x
  return float(np.array([i,j])@L@np.array([i,j])/2+np.array([u,v])@A@np.array([u,v])/2+p['Cb']*b*b/2+q*q+z*z)
 E0=energy(state);y=np.r_[state,np.zeros(9)];t=t0;switches=0
 def rhs(t,y,on):
  i,j,u,v,b,q,z=y[:7];drive=2*np.sin(t)
  sr=p['source_amp']*np.cos(p['omega']*t+phi) if inc else 0.
  si=p['source_amp']*np.sin(p['omega']*t+phi) if inc else 0.
  ju=max((u-b-p['Vd'])/p['Rd'],0.);jv=max((v-b-p['Vd'])/p['Rd'],0.)
  ids=li@np.array([drive-p['R1']*i,u-v-p['R2']*j])
  uv=ai@np.array([-j-ju+p['k']*q,j-jv])
  bd=(ju+jv-(p['Gbleed']+p['Gspark']*on)*b)/p['Cb']
  qd=p['omega']*z-(p['gamma_internal']+p['gamma_rad'])*q-p['k']*u/2+rad*sr
  zd=-p['omega']*q-(p['gamma_internal']+p['gamma_rad'])*z+rad*si
  out=(sr-rad*q)**2+(si-rad*z)**2
  watts=[drive*i,sr*sr+si*si,out,p['R1']*i*i,p['R2']*j*j,
    p['Vd']*(ju+jv)+p['Rd']*(ju*ju+jv*jv),p['Gbleed']*b*b,
    p['Gspark']*on*b*b,2*p['gamma_internal']*(q*q+z*z)]
  return np.r_[ids,uv,bd,qd,zd,watts]
 for _ in range(1000):
  if t>=t0+T-1e-9:break
  def event(t,y):return y[4]-(p['Voff'] if active else p['Von'])
  event.terminal=True;event.direction=-1 if active else 1
  sol=solve_ivp(lambda t,y:rhs(t,y,active),(t,t0+T),y,events=event,rtol=2e-9,atol=3e-11,max_step=.12)
  assert sol.success,sol.message
  t=float(sol.t[-1]);y=sol.y[:,-1]
  if len(sol.t_events[0]):active=not active;switches+=1
  else:break
 else:raise RuntimeError('switching overflow')
 wd,wi,wo,w1,w2,wdi,wbl,wsp,wfi=y[7:];E1=energy(y[:7])
 resid=wd+wi+E0-(wo+w1+w2+wdi+wbl+wsp+wfi+E1)
 assert abs(resid)<1e-6
 return y[:7],active,dict(driver=wd,incident=wi,outgoing=wo,net_wave=wi-wo,spark=wsp,
         diode=wdi,heat=w1+w2+wbl+wfi,storage_delta=E1-E0,residual=resid,switches=switches)
def restored(p,inc,phi):
 x=np.zeros(7);on=False
 for n in range(28):
  y,after,r=advance(p,inc,phi,x,on,n*T)
  err=float(np.max(np.abs(y-x)))
  if err<2e-6 and after==on:
   z,after2,result=advance(p,inc,phi,y,after,(n+1)*T)
   close=max(err,float(np.max(np.abs(z-y))))
   assert after2==after and close<2e-6
   return dict(cycles=n+2,closure=close,**result)
  x=y;on=after
 raise AssertionError('not restored')
def main():
 variants=[('baseline',False,0,{}),('phase0',True,0,{}),('phase90',True,math.pi/2,{}),
 ('phase180',True,math.pi,{}),('phase270',True,3*math.pi/2,{}),('k0',True,0,{'k':0.}),
 ('k030',True,0,{'k':.30}),('Vd015',True,0,{'Vd':.15}),
 ('Gspark15',True,0,{'Gspark':1.5}),('lowSparkThreshold',False,0,{'Von':.003,'Voff':.0009})]
 rows=[]
 for name,inc,phi,changes in variants:
  r=restored(P|changes,inc,phi);r.update(case=name,phase=phi,changed=changes)
  rows.append(r);print(name,'spark',r['spark'],'driver',r['driver'],'net',r['net_wave'])
 checks=0
 for r in rows:
  assert r['closure']<2e-6;checks+=1
  assert abs(r['residual'])<1e-6;checks+=1
  assert abs(r['storage_delta'])<1e-5;checks+=1
  assert abs(r['incident']-r['outgoing']-r['net_wave'])<1e-7;checks+=1
 assert rows[0]['incident']==0;checks+=1
 assert rows[5]['incident']>0 and rows[5]['spark']==0;checks+=1
 assert rows[-1]['spark']>0 and rows[-1]['switches']>0;checks+=1
 result=dict(acceptance=f'{checks}/{checks} PASS',period=T,source_status='synthetic only',cases=rows)
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
