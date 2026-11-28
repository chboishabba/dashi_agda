import numpy as np
from scipy.linalg import expm, eigvals, solve_continuous_lyapunov
from numpy.polynomial.legendre import leggauss
C=np.array([[1.,-1.],[0,1.]])
def run(y0,y1,g,theta=np.pi/2,c=None,d=0., cycles=(1,10,100,1000)):
 Y=np.array([y0,y1]);root=np.sqrt(Y);n=9 if c else 8;A=np.zeros((n,n));B=np.zeros((n,2));B[:2]=np.diag(root) # 2 sqrt(Y)/eps
 A[:2,:2]=-np.diag([.2+y0,.2+y1+g])/2;A[:2,2:4]=C/2;A[:2,6:8]=-np.eye(2)/2;A[2:4,:2]=-C.T/1.5;A[2:4,2:4]=-d*np.eye(2);A[4:6,6:8]=np.eye(2);A[6:8,:2]=1.5*np.eye(2);A[6:8,4:6]=-4*np.eye(2);A[6:8,6:8]=-2/3*np.eye(2)
 if c:A[1,8]=g/2;A[8,1]=g/c;A[8,8]=-g/c
 mass=np.diag([2,2,1.5,1.5,8/3,8/3,2/3,2/3]+([c] if c else []));aug=np.zeros((n+2,n+2));aug[:n,:n]=A;aug[:n,n:]=B;E=expm(.1*aug);T=E[:n,:n];F=E[:n,n:];mon=np.linalg.matrix_power(T,4)
 # External input bins (0,0),(1,0),(0,1),(0,0); delay aligns at bin 2.
 u=np.sqrt(2)*np.array([np.cos(theta),np.sin(theta)]);source=[np.zeros(2),np.zeros(2),u,np.zeros(2)]
 v=np.zeros(n)
 for a in source:v=T@v+F@a
 z0=np.linalg.solve(np.eye(n)-mon,v)
 # exact-in-form integral via continuous Lyapunov/Sylvester of augmented affine flow; use quadrature as independent numerical eval; split at fast decay.
 xs,ws=leggauss(48); pieces=np.unique(np.r_[0.,np.geomspace(1e-7,.1,18),.1]); Q=[((hi-lo)*w/2,expm((lo+(x+1)*(hi-lo)/2)*aug)[:n,:]) for lo,hi in zip(pieces[:-1],pieces[1:]) for x,w in zip(xs,ws)]
 def ledger(z):
  init=z.copy();out=np.zeros(6)
  for a in source:
   out[0]+=.1*(a@a)
   for w,E in Q:
    mid=E@np.r_[z,a];e=mid[:2];h=mid[2:4];vv=mid[6:8];b=root*e-a
    out[1:]+=w*np.array([b@b,g*(e[1]-(mid[8] if c else 0))**2,.2*(e@e),4/9*(vv@vv),1.5*d*(h@h)])
   z=T@z+F@a
  delta=(z@mass@z-init@mass@init)/2;return dict(zip(['incident','reflected','terminal','ohmic','relaxation','magnetic'],out.tolist()))|{'storage':delta,'residual':out[0]-sum(out[1:])-delta,'eta':out[2]/out[0],'state_return_error':float(np.linalg.norm(z-init))}
 p=ledger(z0);first=ledger(np.zeros(n)); decay=-max(eigvals(A).real); rho=max(abs(eigvals(mon)));return dict(y0=y0,y1=y1,g=g,theta=theta,c=c,d=d,decay=float(decay),rho=float(rho),period=p,cold=first,mismatch={str(k):float(np.linalg.norm(np.linalg.matrix_power(mon,k)@z0)/np.linalg.norm(z0)) for k in cycles})
if __name__=='__main__':
 for p in [(200,200,204,1.59518,None,0),(.1,400,400,np.pi/2,None,0),(.1,250,270,np.pi/2,1000,0),(.1,200,204,np.pi/2,None,.01),(.1,200,204,np.pi/2,None,.1),(.1,400,400,np.pi/2,None,.1),(.1,1000,1000,np.pi/2,None,.1),(.1,400,400,np.pi/2,None,.3),(.1,1000,1000,np.pi/2,None,.3)]:
  a=run(*p);print(p,a['period']['eta'],a['decay'],a['period']['magnetic'],a['period']['residual'],a['cold']['eta'],flush=True)
