"""Fixed-normal-space continuous-time energy/receiver dual bound; not RK4 stability."""
import numpy as np
from math import sqrt
from check_f8_geometric_adjoint import Solver

def run():
 S=Solver(180,20,3,.0025);fe=S.fe;M,C,K,b,v,a,g=S.stage[-1];Md,Cd,_=fe.matrices(b,v,True)
 dense=lambda A:fe.mv(A,np.eye(fe.n));M,C,K,Md,Cd=map(dense,(M,C,K,Md,Cd));c=1-v*v;t=S.t;J=-1/(t*sqrt(1+t*t));V=sqrt(1+t*t)/t
 D=np.zeros_like(M);D[-1,-1]=(b+fe.Y[-1])**-3
 m0=np.linalg.eigvalsh(M)[0];assert m0>0
 B0=np.linalg.norm(np.linalg.solve(M,-c*K+a*C+v*Cd),2)
 B1=np.linalg.norm(np.linalg.solve(M,v*(C-C.T)-Md-D),2)
 e0,e1,e2=[np.linalg.norm(fe.evaluate(np.eye(fe.n),0,j)) for j in range(3)]
 limits={'E4':(b*b*e0/4,b*b*abs(J)*e0/4,b*b*V*V*e0/4),'E5_SMS':(b*b*e0/2,b*b*abs(J+2*V)*e0/2,b*b*V*V*e0/2),'E5_direct':(b*b*(e0/6+abs(a)*(v*v/(2*c)+1/6)*e1+c*e2/3),b*b*2*abs(v)*e1/3,b*b*(v*v/(2*c)+1/6)*e0)}
 W,_,_=S.weights();active=S.k>=1
 for name,(Cu,Cv,Ca) in limits.items():
  w=W[name];k=S.k[active];l=S.terminal(w);B=sqrt(2/m0)*(Cu+Cv+Ca*(1+B0+B1));ratios=[]
  for j in np.flatnonzero(active):
   lu,lm=l[:,:,j];z=lu-v*C.T@lm;A=c*K+S.k2[j]*M
   dual=sqrt(2*(z@np.linalg.solve(A,z)+lm@M@lm));ratios.append(dual/(B*S.k[j]**5))
  assert max(ratios)<=1+1e-10
  print(name,'B_FE',B,'max exact modal dual / bound',max(ratios))
 print('PASS fixed-space receiver dual upper bound for',int(active.sum()),'modes per receiver; mesh-uniform Weyl trace remains open')
if __name__=='__main__':run()
