from fractions import Fraction as F
from math import lcm
import numpy as np
from check_ym_p33_configured_contractions_20261119 import SITES,N,O,green,diff
from check_ym_p33_fourier_vertices_20261119 import phase,shift
# Actual reduced inverse: mean-zero source e_y-e_anchor; subtract value at anchor.
D=lcm(*(green(x).denominator for x in SITES)); idx={x:i for i,x in enumerate(SITES)}
C=np.array([[int(D*green(diff(x,y))) for y in SITES] for x in SITES],dtype=np.int64)
L=np.eye(N,dtype=np.int64)*8
for i,x in enumerate(SITES):
 for a in range(4):
  y=idx[shift(x,a)]; L[i,y]-=1;L[y,i]-=1
J=np.array([[0,0,0],[0,0,-2],[0,2,0]],dtype=np.int64)
I=np.eye(3,dtype=np.int64)
def inverse(anchor):
 ids=[i for i in range(N) if i!=anchor]
 K=C[np.ix_(ids,ids)]-C[ids,anchor,None]-C[anchor,ids][None,:]+C[anchor,anchor]
 assert np.array_equal(L[np.ix_(ids,ids)]@K,D*np.eye(N-1,dtype=np.int64))
 return ids,np.kron(K,I)
def jets(axis,p,part):
 A=np.zeros((3*N,3*N),dtype=np.int64); B=A.copy()
 for i,x in enumerate(SITES):
  j=idx[shift(x,axis)]; a=phase(p,x)[part]
  A[3*i:3*i+3,3*j:3*j+3]-=a*J
  A[3*j:3*j+3,3*i:3*i+3]+=a*J
  B[3*i:3*i+3,3*j:3*j+3]-=a*a*(J@J)
  B[3*j:3*j+3,3*i:3*i+3]-=a*a*(J@J)
 return A,B
# -logdet mixed second derivative on equal real direction: tr(K A K A)-tr(K B)
def evaluate(axis,p,anchor):
 ids,K=inverse(anchor); rows=[3*i+c for i in ids for c in range(3)]
 total=F(0)
 for part in (0,1):
  A,B=jets(axis,p,part); A=A[np.ix_(rows,rows)];B=B[np.ix_(rows,rows)]
  # sparse multiplication using nonzero entries
  X=np.zeros_like(K)
  for i,j in zip(*np.nonzero(A)):X[i,:]+=A[i,j]*K[j,:]
  # Python integer accumulation avoids overflow
  t=sum(int(x)*int(y) for x,y in zip(X.flat,X.T.flat))
  u=sum(int(B[i,j])*int(K[j,i]) for i,j in zip(*np.nonzero(B)))
  total+=F(t,D*D)-F(u,D)
 return total
if __name__=='__main__':
 for axis,p in [(0,O),(1,(1,0,0,0)),(0,(1,0,0,0)),(0,(1,1,0,0))]:
  v=evaluate(axis,p,0);w=evaluate(axis,p,17)
  assert v==w,(axis,p,v,w)
  print(axis,p,v,flush=True)
 print('PASS anchored inverse and anchor invariance at selected modes')
