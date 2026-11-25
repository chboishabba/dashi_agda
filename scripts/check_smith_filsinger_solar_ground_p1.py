"""Conditional planar spectral source-to-ground loaded port, not GAMERA replay.
RMS e^{i wt}, downward z, horizontal k along x; fields (TM,TE),
H components power-conjugate to tangential E. Upper Alfvén admittance is
an illustrative scalar two-polarization boundary surrogate, not full MHD.
"""
import json
import numpy as np
import sympy as s
mu=4*np.pi*1e-7; eps=8.8541878128e-12
# Scalar real conductance reverse solve, retain complex signed impedance.
g,R,X,V=s.symbols('g R X V', positive=True, real=True)
p=g*V/((1+g*R)**2+(g*X)**2)
assert s.factor(s.diff(p,g)-V*(1-g*g*(R*R+X*X))/((1+g*R)**2+(g*X)**2)**2)==0
H=s.Matrix([[0,-1],[1,0]]); assert H.T==-H

def operator(f,lam_km,sp,sh,sigma,h=110e3,va=1e6):
    w=2*np.pi*f;k=2*np.pi/(lam_km*1e3);ya=1/(mu*va)
    def adm(cond):
        q=np.sqrt(complex(k*k+1j*w*mu*cond-w*w*mu*eps))
        return q,np.array([(cond+1j*w*eps)/q,q/(1j*w*mu)])
    qa,y=adm(0);_,yg=adm(sigma)
    C=np.eye(2)*np.cosh(qa*h);S=np.sinh(qa*h)
    D=np.diag(S/y);F=np.diag(S*y);Yg=np.diag(yg)
    sheet=np.array([[sp,-sh],[sh,sp]],float);U=ya*np.eye(2)+sheet
    M=U@(C+D@Yg)+F+C@Yg;N=U@D+C
    Z=np.linalg.solve(M,N); assert np.min(np.linalg.eigvalsh((Z+Z.conj().T)/2))>0
    return ya,C,D,F,Yg,sheet,M,Z

def world(op,theta,G,source):
    ya,C,D,F,Yg,sheet,M,Z=op
    u=np.array([np.cos(theta),np.sin(theta)]);ei=np.array([source,0.],complex)
    eg0=np.linalg.solve(M,2*ya*ei);z=u@Z@u;v=u@eg0/(1+G*z);jl=G*u*v
    eg=eg0-Z@jl;hg=Yg@eg+jl;es=C@eg+D@hg;hs=F@eg+C@hg
    inc=ya*np.vdot(ei,ei).real;ref=ya*np.vdot(es-ei,es-ei).real
    ion=np.vdot(es,sheet@es).real;soil=np.vdot(eg,Yg@eg).real;load=G*abs(v)**2
    air=np.vdot(es,hs).real-np.vdot(eg,hg).real
    err=inc-ref-ion-soil-load
    assert abs(air)<1e-9 and abs(err)<1e-9 and min(ion,soil,load,ref)>=-1e-12
    assert np.linalg.norm(2*ya*ei-(ya*np.eye(2)+sheet)@es-hs)<1e-7
    return dict(incident=inc,reflected=ref,natural_net=inc-ref,ionosphere_heat=ion,soil_heat=soil,load=load,energy_residual=err,air_residual=air,ground_E=[abs(t) for t in eg],port_Z=[z.real,z.imag])
rows=[]
for f in (.005,.05):
 for lam in (100,1000,10000):
  for sp in (3,5,20):
   for sh in (0,5):
    for sigma in (.001,.01,.1):
     op=operator(f,lam,sp,sh,sigma);ya,*_=op;Z=op[-1];M=op[-2]
     # Optimize real load direction on fixed resource rank-one homogenized surface port.
     # Signed complex voltage and impedance retained. 181 angles, no global proof.
     best=None
     for theta in np.linspace(0,np.pi,181):
      u=np.array([np.cos(theta),np.sin(theta)]);z=u@Z@u;G=1/abs(z);eg0=np.linalg.solve(M,[2*ya,0]);cap=abs(u@eg0)**2/(2*(abs(z)+z.real))
      if best is None or cap>best[0]:best=(cap,theta,G,z,abs(u@eg0)**2/(4*z.real))
     cap,theta,G,z,conjugate=best
     worlds={label:world(op,theta,G*(1 if ctrl else .1),src) for label,ctrl,src in [('A',0,0),('B',1,0),('C',0,1),('D',1,1)]}
     C=worlds['C'];D=worlds['D'];assert abs(D['load']-cap)<1e-10;assert worlds['A']['load']==worlds['B']['load']==0
     rows.append(dict(f_Hz=f,lambda_km=lam,Pedersen_S=sp,Hall_S=sh,soil_S_m=sigma,theta_deg=theta*180/np.pi,G_opt_S=G,worlds=worlds,load_fraction=D['load']/D['incident'],delta_natural_fraction=(D['natural_net']-C['natural_net'])/D['incident'],incremental_control_budget_fraction=(D['load']-C['load'])/D['incident'],conjugate_match_fraction=conjugate/D['incident']))
sel=[r for r in rows if r['f_Hz']==.005 and r['Pedersen_S']==5 and r['Hall_S']==5 and r['soil_S_m']==.01]
print(json.dumps(dict(status='CONDITIONAL_LOADED_PLANAR_TRANSFER',cases=len(rows),worlds=4*len(rows),max_energy_residual=max(abs(w['energy_residual']) for r in rows for w in r['worlds'].values()),max_air_residual=max(abs(w['air_residual']) for r in rows for w in r['worlds'].values()),selected=sel,maximum=max(rows,key=lambda r:r['load_fraction']),minimum=min(rows,key=lambda r:r['load_fraction']),all_rows=rows,scope='Declared planar fixtures, not fitted to Lin et al.; infinite uniform sheet per-area normalization; ideal scalar upper admittance, homogeneous soil, no actual HF material mechanism or discrete antenna. A/B zero by construction. No physical extraction.'),indent=2))
