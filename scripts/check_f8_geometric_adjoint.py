"""F8 geometry-first hp RK4 adjoint; finite reference, not continuum certification."""
import numpy as np
import sympy as s
from scipy.linalg import solve_banded
from scipy.optimize import brentq
from scipy.special import spherical_jn
from math import asinh,sqrt,ceil
from check_f8_geometry_hp import FE,spectrum

def exact():
 x,y,z=s.symbols('x y z');xyz=(x,y,z);f=(x*x+y*y+z*z)**3
 lap=lambda a:sum(a.diff(d,2) for d in xyz)
 P=lambda i,j,a:(lap(a) if i==j else 0)-a.diff(xyz[i],xyz[j])
 H=s.Matrix(3,3,lambda i,j:s.expand(P(i,1,P(j,1,f))-P(i,2,P(j,2,f))-P(i,j,P(1,1,f)-P(2,2,f))/2))
 assert s.trace(H)==0 and all(s.expand(sum(H[i,j].diff(xyz[i]) for i in range(3)))==0 for j in range(3))
 assert lap(H[1,1])==2016 and H[1,1].diff(x,2)==1056
 t=s.symbols('t',positive=True);A,B,L,F,Fd,R=s.symbols('A B L F Fd R')
 v=-1/s.sqrt(1+t*t);b=1/t;a=t**3/(1+t*t)**2;c=1-v*v;S=s.sqrt(1+t*t)/t
 D=(F-v*A)/c;E=(Fd-v*B+2*v*a*D-a*A)/c;YY=(R+B-2*v*E-(a-3/b)*D-L)/c
 box=-B+2*v*E+c*YY+a*D+L;N=v*v*B+2*v*c*E+c*c*YY-v*v*a*D
 geo=b*b*(-N/(2*c)+box/6);sms=-(S*S*B-A/(t*s.sqrt(1+t*t))+2*S*A-L)/(2*t*t)
 assert s.simplify(geo-sms+(1/t+1/(2*t**3))*F+R/(3*t*t))==0
 print('PASS TT intrinsic Weyl negative control and normal geometric-SMS residual identity',flush=True)

class Solver:
 def __init__(self,n,ne,p,dt,R=4.3,tfinal=11.8):
  self.fe=FE(ne,p);self.k,self.src=spectrum(n,R);self.k2=self.k**2;self.n=n;self.t=tfinal
  F=lambda t:asinh(t)-sqrt(1+t*t)/t;T0=F(1);span=F(tfinal)-T0;self.nt=ceil(span/dt);self.dt=span/self.nt
  self.stage=[]
  for j in range(2*self.nt+1):
   ds=j*self.dt/2;t=brentq(lambda t:F(t)-T0-ds,.5,14);b=1/t;v=-1/sqrt(1+t*t);a=t**3/(1+t*t)**2
   amp=-6*sqrt(1-v*v)/b*np.exp(1-1/(1-(2*ds/.065-1)**2)) if 0<ds<.065 else 0.
   M,C,K=self.fe.matrices(b,v);self.stage.append((M,C,K,b,v,a,-b**-3*amp))
  self.r=sqrt(span**2-(1-1/tfinal)**2)-.012
 def solve(self,M,x):return solve_banded((self.fe.p,self.fe.p),M,x,check_finite=False)
 def rhs(self,x,j,forced=True):
  M,C,K,b,v,a,g=self.stage[j];mv=self.fe.mv;u,m=x
  ut=self.solve(M,m+v*mv(C,u));mt=-v*mv(C,ut,True)-(1-v*v)*mv(K,u)-mv(M,u)*self.k2
  mt[-1]-=(b+self.fe.Y[-1])**-3*ut[-1]
  if forced:mt[0]+=g*self.src
  return np.array([ut,mt])
 def transpose(self,y,j):
  M,C,K,b,v,a,g=self.stage[j];mv=self.fe.mv;alpha,beta=y
  ut=alpha-v*mv(C,beta);ut[-1]-=(b+self.fe.Y[-1])**-3*beta[-1]
  m=self.solve(M,ut);u=v*mv(C,m,True)-(1-v*v)*mv(K,beta)-mv(M,beta)*self.k2
  return np.array([u,m])
 def forward(self):
  dt=self.dt;x=np.zeros((2,self.fe.n,self.n))
  for i in range(self.nt):
   j=2*i;a=self.rhs(x,j);b=self.rhs(x+dt*a/2,j+1);c=self.rhs(x+dt*b/2,j+1);d=self.rhs(x+dt*c,j+2)
   x+=dt*(a+2*b+2*c+d)/6
  assert np.isfinite(x).all();return x
 def jets(self,x):
  j=2*self.nt;M,C,K,b,v,a,g=self.stage[j];Md,Cd,Kd=self.fe.matrices(b,v,True);mv=self.fe.mv
  ut,mt=self.rhs(x,j);utt=self.solve(M,mt+a*mv(C,x[0])+v*mv(Cd,x[0])+v*mv(C,ut)-mv(Md,ut));return np.array([x[0],ut,utt])
 def terminal(self,weights):
  j=2*self.nt;M,C,K,b,v,a,g=self.stage[j];Md,Cd,Kd=self.fe.matrices(b,v,True);mv=self.fe.mv
  u,ut,utt=weights;z=self.solve(M,utt)
  return np.array([u+a*mv(C,z,True)+v*mv(Cd,z,True),np.zeros_like(u)])+self.transpose(np.array([ut+v*mv(C,z,True)-mv(Md,z),z]),j)
 def adjoint(self,lam):
  dt=self.dt;gain=np.zeros(self.n)
  for i in range(self.nt-1,-1,-1):
   j=2*i;l4=dt*lam/6;l3=dt*lam/3;l2=l3.copy();l1=l4.copy();base=lam.copy()
   for stage,l,factor,nxt in ((j+2,l4,dt,l3),(j+1,l3,dt/2,l2),(j+1,l2,dt/2,l1),(j,l1,0,None)):
    gain+=self.stage[stage][-1]*self.src*l[1,0];r=self.transpose(l,stage);base+=r
    if nxt is not None:nxt+=factor*r
   lam=base
  return gain
 def weights(self):
  k=self.k;r=self.r;t=self.t;b=1/t;v=-1/sqrt(1+t*t);a=t**3/(1+t*t)**2;c=1-v*v;S=sqrt(1+t*t)/t;J=-1/(t*sqrt(1+t*t))
  coeff=(.4,-4/7,1/35);ls=(0,2,4)
  sl=sum(d*k**4*spherical_jn(l,k*r) for d,l in zip(coeff,ls))
  d2=sum(d*k**4*((l*(l+1)/r**2-k*k)*spherical_jn(l,k*r)-2*k/r*spherical_jn(l,k*r,True)) for d,l in zip(coeff,ls))
  I=np.eye(self.fe.n);e=[self.fe.evaluate(I,0,j) for j in range(3)]
  def W(u,ut,utt,uy=0,uty=0,uyy=0):return np.array([np.outer(e[0],u)+np.outer(e[1],uy)+np.outer(e[2],uyy),np.outer(e[0],ut)+np.outer(e[1],uty),np.outer(e[0],utt)])
  E4=W(b*b*k*k*sl/4,-b*b*J*sl/4,-b*b*S*S*sl/4)
  old4=W(-b*b*d2/4,-b*b*J*sl/4,-b*b*S*S*sl/4)
  sms=W(-b*b*k*k*sl/2,-b*b*(J+2*S)*sl/2,-b*b*S*S*sl/2)
  flux=W(0*sl,v*sl,0*sl,c*sl)
  bulk=W(-k*k*sl,0*sl,-sl,(a-3/b)*sl,2*v*sl,c*sl)
  direct=W(-b*b*k*k*sl/6,0*sl,b*b*(-v*v/(2*c)-1/6)*sl,b*b*a*(v*v/(2*c)+1/6)*sl,-2*b*b*v*sl/3,-b*b*c*sl/3)
  assert np.linalg.norm(direct-sms+(1/t+1/(2*t**3))*flux+bulk/(3*t*t))<1e-12*np.linalg.norm(direct)
  return dict(E4=E4,legacy4=old4,E5_SMS=sms,E5_direct=direct),flux,bulk
 def run(self):
  rng=np.random.default_rng(1);x=rng.normal(size=(2,self.fe.n,self.n));y=rng.normal(size=x.shape)
  assert np.isclose(np.sum(self.rhs(x,0,False)*y),np.sum(x*self.transpose(y,0)),rtol=1e-11)
  x=self.forward();jets=self.jets(x);W,F,R=self.weights();ans={}
  for name,w in W.items():
   f=np.sum(w*jets,axis=(0,1));g=self.adjoint(self.terminal(w));err=np.linalg.norm(f-g)/max(np.linalg.norm(f),1e-300)
   assert err<1e-8,(name,err);ans[name]=f
   print(name,'forward',f.sum(),'adjoint',g.sum(),'mode relative error',err,'prefix sums',[float(f[:i].sum()) for i in (self.n//4,self.n//2,self.n)],'last-half abs sum',np.abs(f[self.n//2:]).sum(),flush=True)
  print('wall flux',np.sum(F*jets),'bulk residual',np.sum(R*jets),'E5 defect',sum(ans['E5_direct']-ans['E5_SMS']),flush=True)
  assert np.isclose((ans['E5_direct']-ans['E5_SMS']).sum(),-(1/self.t+1/(2*self.t**3))*np.sum(F*jets)-np.sum(R*jets)/(3*self.t**2),atol=1e-10)
  print('PASS all receiver adjoints and off-shell defect ledger',flush=True)

if __name__=='__main__':
 import sys
 exact();n=int(sys.argv[1]) if len(sys.argv)>1 else 180
 Solver(n,20,3,min(.0025,.45/(n*np.pi/4.3))).run()
