"""XCVII: guard-budgeted diplexer on XCVI's native circuit and unchanged pulse.
Numerical diagnostics, not an interval certificate; ideal transducers only.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
os.environ['OMP_NUM_THREADS']='1'
import numpy as np
import sympy as S
from scipy.linalg import expm
from scipy.integrate import solve_ivp
from scipy.optimize import root
import json
Q=S.Rational
# Same J31 off-branch as XCVI, bank b=0 exactly on a periodic off branch.
M=S.Matrix([[2,Q(3,5)],[Q(3,5),Q(3,2)]]);N=S.Matrix([[Q(7,5),-1],[-1,Q(31,20)]])
z=S.Matrix(S.symbols('i j u v q r ih x',real=True));i,j,u,v,q,r,ih,x=z
f=(M.inv()*S.Matrix([-Q(35,100)*i,u-v-Q(28,100)*j])).col_join(N.inv()*S.Matrix([-j+Q(35,100)*q+2*ih,j])).col_join(S.Matrix([Q(11,10)*r-Q(2,10000)*q-Q(35,100)*u/2,-Q(11,10)*q-Q(2,10000)*r,(-x-Q(5,100)*ih-2*u)/Q(15,100),(ih-Q(52,100)*x)/Q(12,100)]))
Ac=f.jacobian(z);K=S.zeros(2,8);K[0,4]=K[1,5]=1
Wc=S.diag(M,N,2,2,Q(15,100),Q(12,100));Dc=S.diag(Q(35,100),Q(28,100),0,0,Q(4,10000),Q(4,10000),Q(5,100),Q(52,100));assert Ac.T*Wc+Wc*Ac==-2*Dc
An=np.array(Ac,float);Kn=np.array(K,float);C=np.array([[1.,-1.],[0.,1.]])
Z0=-.015*Kn@np.linalg.solve(An,Kn.T);U0=np.linalg.solve(-An,Kn.T)[-1];d=np.linalg.solve((Z0+Z0.T)/2,U0);d/=np.linalg.norm(d);t=300*d;e=np.array([0.,1.]);Y=.2*np.eye(2)+20/9*C@C.T+np.outer(e,e)*(t@((Z0+Z0.T)/2)@t);B=Y@e/np.sqrt(Y[1,1]);ev,V=np.linalg.eigh(Y);R=(V*np.sqrt(ev))@V.T;a=R@e/np.linalg.norm(R@e)
p=np.array([.05062544010579979,1.693920383568875,2.3560191376414155,-1.9312719391871591,-3.706267075904543,1.3457281077477645,-4.189915383847338,-.8299539509959512,1.2222486178553746])
Ld,Cd,Ls,Cs,Co,Lo=10**p[3:]
ns=np.arange(1,257);omega=5*np.pi*ns;ak=.25*np.sinc(ns/4)*np.exp(-2j*np.pi*ns*.625);phase=np.exp(2j*np.pi*ns[:,None]*np.linspace(0,1,2049))
def native(w):
 s=1j*w;X=np.linalg.solve(s*np.eye(8)-An,np.sqrt(.03)*Kn.T/2);Z=np.sqrt(.03)*Kn@X;M=(2*s+.2+1.5*s/(s*s+2/3*s+4))*np.eye(2)+C@C.T/(1.5*s+1/(.1*s+20/9))+Y;return s,X,Z,M
cache=[native(w) for w in omega];_,X0,Z,M0=native(0);dc=(X0@t*(e@np.linalg.solve(M0+np.outer(e,e)*(t@Z@t),2*B))).real/4
# Scales alter ONLY the AC input transformer; original source and DC path unchanged.
def params(scale):
 n=np.array([np.cos(p[0]),np.sin(p[0])])*10**p[1];m=10**p[2]*scale;return n,m

def spectral(scale):
 n,m=params(scale);T=np.column_stack((t,n));rows=[]
 for s,X,Z,M in cache:
  zd=1/(s*Ld);za=1/(s*Ls+1/(s*Cs));g=np.column_stack((zd*e,m*za*e));mat=np.zeros((4,4),complex);mat[:2,:2]=M+(zd+m*m*za)*np.outer(e,e);mat[:2,2:]=-g;mat[2:,:2]=-g.T;mat[2:,2:]=np.diag([s*Cd+zd,s*Co+1/(s*Lo)+za])+T.T@Z@T
  v=np.linalg.solve(mat,np.r_[2*B,0.,0.]);rows.append(X@T@v[2:])
 X=np.array(rows);tr=dc[:,None]+2*np.real((X.T*ak)@phase);ac=.52*np.sum(.5*np.sinc(ns/4)**2*abs(X[:,-1])**2);de=4*.52*dc[-1]**2
 # Signed exact identity mean + ripple. Sampled max vs absolute Fourier sum (finite terms only).
 upper=dc[2:4]+2*np.sum(abs(X[:,2:4]*ak[:,None]),axis=0)
 return dict(scale=scale,dc=float(de),ac=float(ac),eta=float(de+ac),sampled_guard=float(np.max(tr[2:4])),finite_harmonic_guard_bound=upper.tolist(),cap_max=float(np.max(abs(tr[-1]))))

def model(scale):
 n,m=params(scale);T=np.column_stack((t,n));A=np.zeros((24,24));Bv=np.zeros(24);Bv[:2]=B
 A[:2,:2]=-(.2*np.eye(2)+Y)/2;A[:2,2:4]=C/2;A[:2,6:8]=-np.eye(2)/2;A[2:4,:2]=-C.T/1.5;A[2:4,8:10]=-np.eye(2)/1.5;A[4:6,6:8]=np.eye(2);A[6:8,:2]=1.5*np.eye(2);A[6:8,4:6]=-4*np.eye(2);A[6:8,6:8]=-2/3*np.eye(2);A[8:10,2:4]=10*np.eye(2);A[8:10,8:10]=-200/9*np.eye(2);A[10:18,10:18]=An
 # Six diplexer coordinates: id, vd, ia, vc, va, io.
 A[1,18]=-1/2;A[1,20]=-m/2;A[18,1]=1/Ld;A[18,19]=-1/Ld;A[19,18]=1/Cd;A[20,1]=m/Ls;A[20,21]=-1/Ls;A[20,22]=-1/Ls;A[21,20]=1/Cs;A[22,20]=1/Co;A[22,23]=-1/Co;A[23,22]=1/Lo
 A[10:18,19]=np.sqrt(.03)*Kn.T@T[:,0]/2;A[10:18,22]=np.sqrt(.03)*Kn.T@T[:,1]/2;A[19,10:18]=-np.sqrt(.03)*T[:,0]@Kn/Cd;A[22,10:18]=-np.sqrt(.03)*T[:,1]@Kn/Co
 mass=np.zeros((24,24));mass[:10,:10]=np.diag([2,2,1.5,1.5,8/3,8/3,2/3,2/3,.1,.1]);mass[10:18,10:18]=np.array(Wc,float);mass[18:,18:]=np.diag([Ld,Cd,Ls,Cs,Co,Lo]);loss=np.zeros((24,24));loss[:2,:2]=.2*np.eye(2)+Y;loss[6:8,6:8]=4/9*np.eye(2);loss[8:10,8:10]=20/9*np.eye(2);loss[10:18,10:18]=np.array(Dc,float)
 assert np.max(abs(A.T@mass+mass@A+2*loss))<1e-7
 return A,Bv,mass

def nonlinear(scale):
 A,Bv,W=model(scale); n=24
 # Similarity scaling by energy mass, improves stiff solve conditioning.
 L=np.linalg.cholesky(W).T;Li=np.linalg.inv(L);F=L@A@Li;Bf=L@Bv
 aug=np.zeros((n+1,n+1));aug[:n,:n]=F;aug[:n,n]=Bf;exp=expm(.1*aug);P=exp[:n,:n];kick=exp[:n,n];guess=np.linalg.solve(np.eye(n)-np.linalg.matrix_power(P,4),P@kick)
 def flow(y,ledger=False):
  y=y.copy();vals=np.zeros(5);gap=-np.inf;capmax=0.
  for k in range(4):
   on=float(k==2)
   def fun(time,Yv):
    y=Yv[:n];z=Li@y;dz=A@z+on*Bv;dz[17]/=1+1.5*z[17]**2
    if not ledger:return L@dz
    e=z[:2];vel=z[6:8];eb=z[8:10];i,j,u,v,q,r,ih,x=z[10:18];out=R@e-on*a
    return np.r_[L@dz,on,out@out,.52*x*x,.2*(e@e)+4/9*(vel@vel)+20/9*(eb@eb),.35*i*i+.28*j*j+.0004*(q*q+r*r)+.05*ih*ih]
   def jac(time,y):
    z=Li@y;J=A.copy();d=1+1.5*z[17]**2;J[17,:]/=d;J[17,17]-=3*z[17]*(A@z+on*Bv)[17]/d**2;return L@J@Li
   sol=solve_ivp(fun,(0,.1),np.r_[y,np.zeros(5)] if ledger else y,method='Radau',rtol=3e-9,atol=3e-11,jac=None if ledger else jac,dense_output=ledger)
   assert sol.success; y=sol.y[:n,-1]
   if ledger:
    vals+=sol.y[n:,-1];tr=Li@sol.sol(np.linspace(0,.1,1001))[:n];gap=max(gap,float(np.max(tr[12:14])));capmax=max(capmax,float(np.max(abs(tr[17]))))
  return (y,vals,gap,capmax) if ledger else y
 # Numerical shooting. No event branch claim until guards are rigorously enclosed.
 res=root(lambda y:flow(y)-y,guess,tol=1e-8);y,vals,gap,capmax=flow(res.x,True);return_error=float(np.max(abs(y-res.x)));z=Li@res.x;zf=Li@y
 energy=lambda z:.5*z@W@z+.12*.375*z[17]**4
 resid=float(vals[0]-sum(vals[1:])-(energy(zf)-energy(z)))
 return dict(scale=scale,root_success=bool(res.success),return_error=return_error,eta=float(vals[2]/vals[0]),ledger=vals.tolist(),ledger_residual=resid,sampled_guard=gap,sampled_cap_max=capmax,linear_decay=float(-max(np.linalg.eigvals(A).real)),sampled_guard_pass=gap<.1,exact_nonlinear_certificate=False)

if __name__=='__main__':
 import sys
 rows=[spectral(float(s)) for s in np.r_[0,np.geomspace(.01,1,31)]]
 for row in rows:print('scan',row,flush=True)
 safe=max((r for r in rows if max(r['finite_harmonic_guard_bound'])<.075),key=lambda r:r['eta']);print('selected',safe,flush=True)
 result=dict(status='NUMERICAL_GUARD_BUDGETED_MATCHING',linear=rows,selected=safe,nonlinear=[],source_unchanged=True,guard_certificate=False,physical_admission=False)
 if '--nonlinear' in sys.argv:
  for s in [safe['scale']]:
   v=nonlinear(s);result['nonlinear'].append(v);print('nonlinear',v,flush=True)
 print('RECEIPT '+json.dumps(result),flush=True)
