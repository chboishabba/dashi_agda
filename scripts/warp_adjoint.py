import numpy as np
from scipy.sparse import coo_matrix,eye,diags,kron,bmat,csr_matrix
from scipy.integrate import quad
import sympy as s
from scipy.optimize import brentq
from math import asinh,sqrt,ceil
# Original source primitives, exactly as fetched, with cell integration.
u=s.symbols('u',positive=True); f=s.exp(1-1/(1-u*u)); d=[f]+[s.diff(f,u,n) for n in range(1,4)]
pr=[s.Rational(2,5)*(u*u*d[3]+2*u*d[2]-2*d[1]),s.Rational(4,7)*(u**4*d[3]-3*u**3*d[2]+3*u**2*d[1]),(u**6*d[3]-12*u**5*d[2]+75*u**4*d[1]-315*u**3*f)/35]
pr=[s.lambdify(u,s.factor(x),'numpy') for x in pr]
def sources(r,dr,eps):
 out=np.zeros((3,len(r)))
 for j,x in enumerate(r):
  lo=max(0,x-dr/2); hi=min(eps,x+dr/2)
  if hi<=lo:continue
  a,b=lo/eps,hi/eps
  for q in range(3):
   dim=3+4*q; mass=(0 if b==1 else pr[q](b))-(0 if a==0 else pr[q](a))
   if q==2:mass+=quad(lambda u:27*u*u*np.exp(1-1/(1-u*u)),a,b)[0]
   out[q,j]=eps**dim*mass/(((x+dr/2)**dim-lo**dim)/dim)
 return out

def run(dr=.04,dy=.06,dt=.008,eps=.16,final=3.,pulse=.15):
 # intentionally reduced finite-grid fixture; not original production grid
 F=lambda t:asinh(t)-sqrt(1+t*t)/t
 t0,te=F(1),F(final); span=te-t0; nt=ceil(span/dt); dt=span/nt
 r=np.arange(ceil(3.1/dr)+1)*dr;y=np.arange(ceil(2.1/dy)+1)*dy; nr=len(r);ny=len(y); n=nr*ny
 src=sources(r,dr,eps); I=eye(n,format='csr'); zero=csr_matrix((n,n)); mask=np.ones((ny,nr));mask[:,-1]=0; Q=diags(mask.ravel()); E=kron(eye(ny),diags(np.r_[np.ones(nr-1),0]));
 # normal SBP2 derivative
 D=np.zeros((ny,ny));D[0,:2]=[-1,1];D[-1,-2:]=[-1,1]
 for j in range(1,ny-1):D[j,j-1]=-0.5;D[j,j+1]=.5
 Dy=kron(csr_matrix(D/dy),eye(nr)).tocsr(); lo=diags(np.repeat(np.r_[1,np.zeros(ny-1)],nr)); hi=diags(np.repeat(np.r_[np.zeros(ny-1),1],nr));
 L=[]
 for q in range(3):
  dim=3+4*q; A=np.zeros((nr,nr)); A[0,:2]=[-2*dim,2*dim]
  for j in range(1,nr-1):
   den=(j+.5)**dim-(j-.5)**dim; p=dim*(j+.5)**(dim-1)/den;m=dim*(j-.5)**(dim-1)/den;A[j,j-1:j+2]=[m,-m-p,p]
  L.append(kron(eye(ny),csr_matrix(A/dr**2)).tocsr())
 def coeff(k):
  T=t0+k*dt; t=brentq(lambda t:F(t)-T,.5,final+2);v=-1/sqrt(1+t*t);b=1/t
  return t,v,b
 def op(q,k):
  t,v,b=coeff(k); a=1+v;c=1-v; Z=diags(np.repeat(1.5/(b+y),nr)); R=L[q]
  A=bmat([[zero,a*I/2,c*I/2],[R,a*Dy-Z-2*a*hi/dy,Z],[R,-Z+2*a*lo/dy,-c*Dy+Z-2*c*lo/dy]],format='csr')
  # target=(a P-2 amp src)/c; M injection -4 amp src/dy
  mask3=diags(np.tile(mask.ravel(),3)); A=mask3@A@mask3
  J=np.zeros(3*n);J[2*n:2*n+nr]=-4*src[q]/dy;J[-n+nr-1]=0
  return eye(3*n,format='csr')+dt*A,dt*J
 # source value at each half step independently; same spatial source all modes
 times=np.arange(2*(nt+1)+1)*dt/2; active=(times>0)&(times<pulse); f0=np.zeros(len(times));f0[active]=np.exp(1-1/np.maximum(1-(2*times[active]/pulse-1)**2,1e-300));
 # use actual temporal amplitude normalization -6 sqrt(1-v²)/b
 for j in np.flatnonzero(active):
  t,v,b=coeff(j/2);f0[j]*=-6*sqrt(1-v*v)/b
 rx=sqrt(span**2-(1-1/final)**2)-.012; ir=int(rx/dr); x=rx/dr-ir
 w=np.array([-x*(x-1)*(x-2)/6,(x+1)*(x-1)*(x-2)/2,-(x+1)*x*(x-2)/2,(x+1)*x*(x-1)/6]);dw=np.array([-(3*x*x-6*x+2)/6,(3*x*x-4*x-1)/2,(-3*x*x+2*x+2)/2,(3*x*x-1)/6])/dr;dd=np.array([1-x,3*x-2,1-3*x,x])/dr**2
 gain=np.zeros(len(times)); S=sqrt(1+final**2)/final
 def obs(q,k):
  z=np.zeros(3*n); ell=2*q; fac=(rx/eps)**ell; co={nt-1:S*S/dt**2+1/(2*dt*final*sqrt(1+final**2)),nt:-2*S*S/dt**2,nt+1:S*S/dt**2-1/(2*dt*final*sqrt(1+final**2))}.get(k,0); a=co*w
  if k==nt:a=a+dd+2*ell*dw/rx+ell*(ell-1)*w/rx**2
  z[ir-1:ir+3]=-fac*a/(4*final**2);return z
 def forward(control):
  val=0.
  for q in range(3):
   x=np.zeros(3*n)
   for k in range(nt+1):
    val+=obs(q,k)@x;B0,j0=op(q,k);B1,j1=op(q,k+1);Bh,jh=op(q,k+.5)
    x1=B0@x+j0*control[2*k];x2=.75*x+.25*(B1@x1+j1*control[2*k+2]);x=x/3+2/3*(Bh@x2+jh*control[2*k+1])
   val+=obs(q,nt+1)@x
  return val
 for q in range(3):
  lam=obs(q,nt+1)
  for k in range(nt,-1,-1):
   B0,j0=op(q,k);B1,j1=op(q,k+1);Bh,jh=op(q,k+.5)
   l2=2/3*(Bh.T@lam);l1=.25*(B1.T@l2)
   gain[2*k+1]+=2/3*(jh@lam);gain[2*k+2]+=.25*(j1@l2);gain[2*k]+=j0@l1
   lam=lam/3+.75*l2+B0.T@l1+obs(q,k)
 gain[~active]=0
 # Integrate the Israel boundary-energy bound in conformal time using
 # the SSPRK3 stage quadrature (shared endpoint samples accumulate).
 weights=np.zeros_like(times)
 for k in range(nt+1):
  weights[2*k:2*k+3]+=dt*np.array([1/6,2/3,1/6])
 for j in range(len(times)):
  t,v,b=coeff(j/2)
  weights[j]*=1/(-v*b**3)
 assert np.all(weights>0)
 budget=np.dot(weights,f0*f0)
 compliance=np.dot(gain,gain/weights)
 assert budget>0 and compliance>0
 opt=gain/weights*np.sqrt(budget/compliance)
 assert np.isclose(np.dot(weights,opt*opt),budget,rtol=1e-12,atol=0)
 a=forward(f0);b=forward(opt);pred=gain@f0;pred2=gain@opt
 assert np.isclose(pred2,np.sqrt(budget*compliance),rtol=1e-12,atol=0)
 print('Israel upper-bound cost',budget,'optimized cost',np.dot(weights,opt*opt),'squared response gain',(pred2/pred)**2,'compliance',compliance,flush=True)
 print('grid',nr,ny,nt,'receiver',rx,'photon margin',rx-eps-np.log(final),'original',a,'adjoint',pred,'optimized',b,'predicted',pred2,'amplitude gain',abs(b/a),'weighted cost',budget,flush=True)
 assert np.isclose(a,pred,rtol=1e-7,atol=1e-9) and np.isclose(b,pred2,rtol=1e-7,atol=1e-9)
if __name__=='__main__':
 import sys,json
 run(**(json.loads(sys.argv[1]) if len(sys.argv)>1 else {}))
