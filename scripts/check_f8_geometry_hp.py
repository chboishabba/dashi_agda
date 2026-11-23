"""Geometry-first hp Galerkin and analytic element jets; reference, not native FV."""
import numpy as np
import sympy as s
from scipy.linalg import solve_banded
from scipy.optimize import brentq
from scipy.special import spherical_jn
from numpy.polynomial.legendre import leggauss
from numpy.polynomial.polynomial import polyder,polyval
from math import asinh,sqrt,ceil
from check_f8_tensor_backreaction import angular

def geometry():
 b,L=s.symbols('b L',positive=True);v,pi=s.symbols('v pi',real=True);g=L**2/b**2*s.diag(-1,1);gamma=1/s.sqrt(1-v*v)
 t=b/L*gamma*s.Matrix([1,v]);n=b/L*gamma*s.Matrix([v,1])
 assert s.simplify((t.T*g*t)[0]+1)==s.simplify((n.T*g*n)[0]-1)==s.simplify((t.T*g*n)[0])==0
 assert s.simplify(b/L*gamma*(-6*L/b/gamma*pi)+6*pi)==0
 print('unit normal, tangent, orthogonality, physical Israel normalization PASS',flush=True)

def spectrum(n,R=4.3,eps=.04,nq=320):
 x,w=leggauss(nq);u=(x+1)/2;w=w/2;k=np.arange(1,n+1)*np.pi/R
 return k,2/R*k*(np.sin(k[:,None]*eps*u)@(w*u*eps**6*np.exp(1-1/(1-u*u))))

def tails(R=4.3,eps=.04):
 u=s.symbols('u',real=True);f=u*s.exp(1-1/(1-u*u));x,w=leggauss(480);x=(x+1)/2;w=w/2;k,c=spectrum(2880,R,eps,480);_,c2=spectrum(2880,R,eps,320)
 for j in (4,6):
  D=s.lambdify(u,s.diff(f,u,j),'numpy');total=eps**(11-2*j)*np.dot(w,D(x)**2);modal=R/2*(c*k**(j-1))**2
  print('source derivative order',j,'total',total,'tail fractions',[(n,float(1-modal[:n].sum()/total)) for n in (180,360,720,1440,2880)],'quad relative difference',np.linalg.norm((c-c2)*k**(j-1))/np.linalg.norm(c*k**(j-1)),flush=True)

class FE:
 def __init__(self,ne,p):
  self.p=p;self.ne=ne;self.h=2.1/ne;self.Y=np.linspace(0,2.1,ne*p+1);self.idx=np.arange(ne)[:,None]*p+np.arange(p+1);self.n=len(self.Y)
  x,w=leggauss(max(8,2*p+3));x=(x+1)/2;self.g=w/2*self.h;self.poly=np.linalg.inv(np.vander(np.linspace(0,1,p+1),p+1,increasing=True)).T
  self.phi=np.array([polyval(x,c) for c in self.poly]);self.dphi=np.array([polyval(x,polyder(c))/self.h for c in self.poly]);self.offset=self.Y[self.idx[:,0],None]+self.h*x
  self.rows=(p+self.idx[:,:,None]-self.idx[:,None,:]).ravel();self.cols=np.broadcast_to(self.idx[:,None,:],(ne,p+1,p+1)).ravel()
 def matrices(self,b,v,derivative=False):
  W=(b+self.offset)**-3*self.g
  if derivative:W=W*(-3*v/(b+self.offset))
  mats=[]
  for f,g in ((self.phi,self.phi),(self.phi,self.dphi),(self.dphi,self.dphi)):
   a=np.einsum('eq,iq,jq->eij',W,f,g);ab=np.zeros((2*self.p+1,self.n));np.add.at(ab,(self.rows,self.cols),a.ravel());mats.append(ab)
  return mats
 def mv(self,A,x,transpose=False):
  p=self.p;y=A[p,:,None]*x
  for k in range(1,p+1):
   if transpose:y[k:]+=A[p-k,k:,None]*x[:-k];y[:-k]+=A[p+k,:-k,None]*x[k:]
   else:y[:-k]+=A[p-k,k:,None]*x[k:];y[k:]+=A[p+k,:-k,None]*x[:-k]
  return y
 def evaluate(self,U,Y,d=0):
  e=min(self.ne-1,int(Y/self.h));x=Y/self.h-e;w=np.array([polyval(x,polyder(c,d))/self.h**d for c in self.poly]);return w@U[self.idx[e]]

def evolve(ne,p,n,dt,R=4.3,tfinal=11.8,manufactured=False):
 fe=FE(ne,p);k,src=spectrum(n,R);F=lambda t:asinh(t)-sqrt(1+t*t)/t;T0=F(1);span=F(tfinal)-T0
 if manufactured:k=np.array([0.]);src=np.array([0.]);n=1;span=.3
 nt=ceil(span/dt);dt=span/nt;U=np.zeros((fe.n,n));m=np.zeros_like(U)
 if manufactured:U[:,0]=(1+fe.Y)**4
 def rhs(U,m,T,jets=False):
  t=brentq(lambda t:F(t)-T,.5,14);b=1/t;v=-1/sqrt(1+t*t);a=t**3/(1+t*t)**2;ds=T-T0
  amp=-6*sqrt(1-v*v)/b*np.exp(1-1/(1-(2*ds/.065-1)**2)) if 0<ds<.065 else 0.
  M,C,K=fe.matrices(b,v);mv=fe.mv;Ut=solve_banded((p,p),M,m+v*mv(C,U),check_finite=False)
  mt=-v*mv(C,Ut,True)-(1-v*v)*mv(K,U)-mv(M,U)*k*k
  if manufactured:mt[0]-=4.;mt[-1]+=4.
  else:mt[0]-=b**-3*amp*src;mt[-1]-=(b+fe.Y[-1])**-3*Ut[-1]
  if jets:
   Md,Cd,Kd=fe.matrices(b,v,True);Utt=solve_banded((p,p),M,mt+a*mv(C,U)+v*mv(Cd,U)+v*mv(C,Ut)-mv(Md,Ut),check_finite=False);return Ut,Utt,b,v,a,amp
  return Ut,mt
 for j in range(nt):
  T=T0+j*dt;A,B=rhs(U,m,T);C,D=rhs(U+dt*A/2,m+dt*B/2,T+dt/2);E,G=rhs(U+dt*C/2,m+dt*D/2,T+dt/2);H,I=rhs(U+dt*E,m+dt*G,T+dt)
  U+=dt*(A+2*C+2*E+H)/6;m+=dt*(B+2*D+2*G+I)/6
  if j%100==0:assert np.isfinite(U).all()
 Ut,Utt,b,v,a,amp=rhs(U,m,T0+span,True);assert np.isfinite(Utt).all()
 if manufactured:
  err=np.max(abs(U[:,0]-(b+fe.Y)**4));print('manufactured',ne,p,dt,err,flush=True);return err
 r=2.52;Y=.061;xyz,polys=angular();point=r*np.array([2.,3.,6.])/7;shapes=np.array([np.array(P.subs(dict(zip(xyz,point))),float) for P in polys]);ell=(0,2,4);coeff=(.4,-4/7,1/35)
 B=np.array([c*k**4*spherical_jn(l,k*r)/r**l for c,l in zip(coeff,ell)]);lift=lambda A:np.einsum('lk,k,lij->ij',B,A,shapes)
 u=fe.evaluate(U,Y);uy=fe.evaluate(U,Y,1);uyy=fe.evaluate(U,Y,2);ut=fe.evaluate(Ut,Y);uty=fe.evaluate(Ut,Y,1);utt=fe.evaluate(Utt,Y)
 wave=-utt+2*v*uty+(1-v*v)*uyy+(a-3/(b+Y))*uy-k*k*u;H=lift(u)/(b+Y)**2;E=-lift(wave)/2
 wall=fe.evaluate(U,0);wallt=fe.evaluate(Ut,0);walltt=fe.evaluate(Utt,0);wally=fe.evaluate(U,0,1);flux=(1-v*v)*wally+v*wallt-amp*src
 rx=sqrt((F(tfinal)-F(1))**2-(1-1/tfinal)**2)-.012;sl=np.array([c*k**4*spherical_jn(l,k*rx) for c,l in zip(coeff,ell)]).sum(axis=0)
 d2=np.array([c*k**4*((l*(l+1)/rx**2-k*k)*spherical_jn(l,k*rx)-2*k/rx*spherical_jn(l,k*rx,True)) for c,l in zip(coeff,ell)]).sum(axis=0)
 S=sqrt(1+tfinal*tfinal)/tfinal;Heta=S*(sl@wallt);Hetaeta=S*S*(sl@walltt)-(sl@wallt)/(tfinal*sqrt(1+tfinal*tfinal));E4=-(Hetaeta+d2@wall)/(4*tfinal*tfinal);E5=-(Hetaeta+2*Heta+sl@(k*k*wall))/(2*tfinal*tfinal)
 out=dict(ne=ne,p=p,n=n,dt=dt,h=float(np.linalg.norm(H)),E=float(np.linalg.norm(E)),relative=float(np.linalg.norm(E)/np.linalg.norm(H)),wall_flux=float(np.linalg.norm(lift(flux))),E4=float(E4),E5=float(E5));print(out,flush=True);return out

if __name__=='__main__':
 import sys,json
 if sys.argv[1]=='verify':geometry();tails();evolve(20,1,1,.001,manufactured=True);evolve(20,3,1,.001,manufactured=True);evolve(20,4,1,.001,manufactured=True)
 else:
  for case in json.loads(sys.argv[1]):evolve(*case)
