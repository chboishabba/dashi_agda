#!/usr/bin/env python3
"""J11 nonlinear S3 capacitive-return + S5 radiative dipole ledger.
Synthetic dimensionless study; no Filsinger physical pin/source attribution.
"""
import numpy as np
import sympy as s
from scipy.integrate import solve_ivp
import json
P=dict(L1=2.,L2=1.5,M=.6,R1=.35,R2=.28,C=1.,Cu=.4,Cv=.55,Cb=.65,
       Rd=.12,Vd=.1,Gbleed=.018,Gspark=1.1,Von=.22,Voff=.075,
       omega=1.1,gamma_rad=.085,gamma_internal=.04,k=.15,source_amp=.10)
L=np.array([[P['L1'],P['M']],[P['M'],P['L2']]])
A=np.array([[P['C']+P['Cu'],-P['C']],[-P['C'],P['C']+P['Cv']]])
assert min(np.linalg.eigvalsh(L))>0 and min(np.linalg.eigvalsh(A))>0
Li=np.linalg.inv(L);Ai=np.linalg.inv(A)
# Analytical identity: magnetic, capacitive, field, and bank derivatives.
i,j,u,v,b,q,p,V,F,G,gi,gr,k,om,di,dj,z,h=s.symbols('i j u v b q p V F G gi gr k om di dj z h',real=True)
L1,L2,M,C,Cu,Cv,Cb,R1,R2=s.symbols('L1 L2 M C Cu Cv Cb R1 R2',real=True)
Lm=s.Matrix([[L1,M],[M,L2]]); Am=s.Matrix([[C+Cu,-C],[-C,C+Cv]])
der=list(Lm.inv()*s.Matrix([V-R1*i,u-v-R2*j]))+list(Am.inv()*s.Matrix([-j-di+k*q,j-dj]))+[(di+dj-(z+h)*b)/Cb,
 om*p-(gi+gr)*q-k*u/2+F,-om*q-(gi+gr)*p+G]
st=[i,j,u,v,b,q,p]
energy=(s.Matrix([i,j]).T*Lm*s.Matrix([i,j]))[0]/2+(s.Matrix([u,v]).T*Am*s.Matrix([u,v]))[0]/2+Cb*b*b/2+q*q+p*p
edot=sum(s.diff(energy,x)*dx for x,dx in zip(st,der))
expected=V*i+2*(q*F+p*G)-R1*i*i-R2*j*j-(u-b)*di-(v-b)*dj-(z+h)*b*b-2*(gi+gr)*(q*q+p*p)
assert s.simplify(edot-expected)==0
sr,si,r=s.symbols('sr si r',real=True)
pout=(sr-r*q)**2+(si-r*p)**2
assert s.simplify((sr*sr+si*si-pout)-(2*r*(q*sr+p*si)-r*r*(q*q+p*p)))==0
assert s.simplify(s.diff(edot-expected,k))==0
checks=3

def run(label,driver=True,incident=False,precharge=0.,periods=8):
    # 7 system states followed by 9 separately integrated work channels.
    y=np.zeros(16);y[4]=precharge;on=precharge>=P['Von'];t=0.;T=periods*2*np.pi;switches=0
    def rhs(time,y,on):
        i,j,u,v,b,q,p=y[:7]
        V=2*np.sin(time) if driver else 0.
        sr=P['source_amp']*np.cos(P['omega']*time) if incident else 0.
        si=P['source_amp']*np.sin(P['omega']*time) if incident else 0.
        di=max((u-b-P['Vd'])/P['Rd'],0.);dj=max((v-b-P['Vd'])/P['Rd'],0.)
        a=np.sqrt(2*P['gamma_rad'])
        ij=Li@np.array([V-P['R1']*i,u-v-P['R2']*j])
        uv=Ai@np.array([-j-di+P['k']*q,j-dj])
        db=(di+dj-(P['Gbleed']+P['Gspark']*on)*b)/P['Cb']
        dq=P['omega']*p-(P['gamma_rad']+P['gamma_internal'])*q-P['k']*u/2+a*sr
        dp=-P['omega']*q-(P['gamma_rad']+P['gamma_internal'])*p+a*si
        pout=(sr-a*q)**2+(si-a*p)**2
        work=[V*i,sr*sr+si*si,pout,P['R1']*i*i,P['R2']*j*j,
              P['Vd']*(di+dj)+P['Rd']*(di*di+dj*dj),
              P['Gbleed']*b*b,P['Gspark']*on*b*b,
              2*P['gamma_internal']*(q*q+p*p)]
        return np.r_[ij,uv,db,dq,dp,work]
    for iteration in range(500):
        if t>=T-1e-10:break
        def event(t,y):return y[4]-(P['Voff'] if on else P['Von'])
        event.terminal=True;event.direction=-1 if on else 1
        sol=solve_ivp(lambda time,x:rhs(time,x,on),(t,T),y,events=event,
                      rtol=3e-10,atol=2e-12,max_step=.05)
        if not sol.success:raise RuntimeError(sol.message)
        t=float(sol.t[-1]);y=sol.y[:,-1]
        if len(sol.t_events[0]):switches+=1;on=not on
        else:break
    else:raise RuntimeError('switching limit exceeded')
    i,j,u,v,b,q,p=y[:7]
    storage=np.array([i,j])@L@np.array([i,j])/2+np.array([u,v])@A@np.array([u,v])/2+P['Cb']*b*b/2+q*q+p*p
    wd,wi,wo,w1,w2,wdi,wbl,wsp,wfi=y[7:]
    initial=P['Cb']*precharge**2/2
    residual=(wd+wi+initial)-(wo+w1+w2+wdi+wbl+wsp+wfi+storage)
    assert abs(residual)<2e-7
    assert min(wo,w1,w2,wdi,wbl,wsp,wfi)>=-1e-9
    return dict(scenario=label,driver_work=float(wd),incident_work=float(wi),
                outgoing_work=float(wo),net_wave_work=float(wi-wo),
                spark_work=float(wsp),diode_heat=float(wdi),ohmic_heat=float(w1+w2),
                internal_field_heat=float(wfi),bleed_heat=float(wbl),
                initial_storage=float(initial),final_storage=float(storage),
                final_bank_energy=float(P['Cb']*b*b/2),work_residual=float(residual),
                spark_transitions=switches)
cases=[run('drive_only'),run('drive_plus_incident',True,True),
       run('incident_only',False,True),run('no_input_empty',False,False),
       run('precharged_only',False,False,.9)]
assert cases[3]['spark_work']==0 and cases[4]['spark_work']>0
assert cases[1]['incident_work']>0 and cases[2]['incident_work']>0
assert cases[1]['outgoing_work']>0 and cases[2]['outgoing_work']>0
assert all(abs(x['work_residual'])<2e-7 for x in cases)
checks+=9
for case in cases:
    assert abs(case['incident_work']-case['outgoing_work']-case['net_wave_work'])<1e-9
    checks+=1
result=dict(title='J11 conditional nonlinear S3/S5 open-field-port comparison',
            acceptance=f'{checks}/{checks} PASS',parameters=P,cases=cases,
            original_FM_pin_proofs='0/4',natural_source_meter='unverified')
print(json.dumps(result,indent=2))
