"""Same slow source as paid actuator: periodic averaged stiffness intervention.
Ideal latch, not demonstrated HF material. No physical source calibration.
"""
import json
import numpy as np
import sympy as S
from scipy.linalg import expm
from scipy.linalg import solve_banded
F,v,rs=S.symbols('F v rs',real=True,positive=True)
assert S.expand(F*v-rs*v*v-(F*F/(4*rs)-rs*(v-F/(2*rs))**2))==0
# q,v,cos,sin, source RMS=1, Rs=RL=1.
def matrices(k,dt,source):
    A=np.array([[0,1,0,0],[-k,-2,np.sqrt(2)*source,0],[0,0,0,-1],[0,0,1,0.]])
    P=expm(A*dt)
    # Integrate all products by an augmented linear system, no sampled quadrature.
    K=np.zeros((18,18));K[:16,:16]=np.kron(A,np.eye(4))+np.kron(np.eye(4),A)
    K[16,5]=1;K[17,6]=np.sqrt(2)*source
    return P,expm(K*dt)[16:,:16]
def run(period,duty,phase,source=1):
    T=2*np.pi*period
    P,J=matrices(1.,T*duty,source);O,K=matrices(.25,T*(1-duty),source)
    total=O@P;clock=np.array([np.cos(phase),np.sin(phase)])
    x=np.r_[np.linalg.solve(np.eye(2)-total[:2,:2],total[:2,2:]@clock),clock]
    y=P@x;z=O@y
    assert np.max(abs(z-x))<1e-9
    a=J@np.kron(x,x)+K@np.kron(y,y)
    load,src=a
    wp=.375*x[0]**2;wm=-.375*y[0]**2;switch=wp+wm
    err=src+switch-2*load
    assert abs(err)<1e-8
    return dict(period=period,duty=duty,phase=phase,source=src/T,load=load/T,switch_positive=wp/T,switch_negative=wm/T,switch_net=switch/T,energy_residual=err/T,periodic_error=float(np.max(abs(z-x))))
def carrier(O,N):
    freq=1+2*np.arange(-N,N+1)*O; ab=np.zeros((3,2*N+1),complex);ab[1]=1-freq**2+2j*freq;ab[0,1:]=.375;ab[2,:-1]=.375
    b=np.zeros(2*N+1,complex);b[N]=1/np.sqrt(2);x=solve_banded((1,1),ab,b);vel=1j*freq*x
    load=2*np.vdot(vel,vel).real;src=2*np.real(np.conj(b[N])*vel[N]);exchange=2*load-src
    return float(load),float(src),float(exchange)
base=16/73;assert abs(run(1,0,0)['load']-base)<1e-12
matched=run(1,1,0);assert abs(matched['load']-.25)<1e-12
rows=[]
for n in (1,4,16,64):
 for duty in (.25,.5,.75,1-1/(2*n)):
  for ph in np.arange(8)*np.pi/4:
   d=run(n,duty,ph);b=run(n,duty,ph,0);assert abs(b['load'])<1e-14
   d['incremental_budget_ideal']=d['load']-d['switch_net']-base
   d['incremental_budget_no_recovery']=d['load']-d['switch_positive']-base
   d['matched_gap']=.25-(d['load']-d['switch_net']);assert d['matched_gap']>=-1e-10
   rows.append(d)
# 1000:1 continuous and averaged intermittent control (same energy scaling).
quality=10000;ratio=1000;maintenance=.75*ratio/quality
for d in rows:
 d['intermittent_net']=d['load']-d['switch_net']-maintenance*d['duty']
 d['latch_extra_cost_per_cycle_budget']=d['incremental_budget_no_recovery']*2*np.pi*d['period']
load,src,exchange=carrier(ratio,8);assert max(abs(a-b) for a,b in zip((load,src,exchange),carrier(ratio,16)))<1e-10
result=dict(status='CONDITIONAL_AVERAGED_LATCH_AND_PASSIVE_BOUND',baseline=base,matched=matched,carrier=dict(load=load,source=src,exchange=exchange,maintenance=maintenance,net=load-exchange-maintenance),cases=len(rows),zero_source_controls=len(rows),max_residual=max(abs(d['energy_residual']) for d in rows),max_periodic_error=max(d['periodic_error'] for d in rows),best_latch=max(rows,key=lambda d:d['incremental_budget_no_recovery']),best_duty=max(rows,key=lambda d:d['intermittent_net']),selected_by_period=[max((d for d in rows if d['period']==n),key=lambda d:d['incremental_budget_no_recovery']) for n in (1,4,16,64)],scope='Piecewise constant averaged stiffness, instantaneous signed switching work, unspecified extra actuator/standby cost; no HF latch realization. Same prescribed force/source damping, not calibrated ground boundary. No claim of universal passive dominance outside this scalar source model.')
print(json.dumps(result,indent=2))
