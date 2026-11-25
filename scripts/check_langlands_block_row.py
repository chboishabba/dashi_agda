"""Exact original row-quotient and conditional Fourier contraction (rank eight)."""
import sympy as s
from itertools import product
from collections import Counter
B=s.Matrix([[6,21],[-7,-15]])/9;P=s.Matrix([[0,-3],[1,3]]);X=s.Matrix.hstack(s.eye(2)[:,0],B[:,0]);Q=[B**i*X*s.diag(3**(7-2*i),3**(6-2*i)) for i in range(4)];q=s.diag(*Q);beta=s.diag(*[B]*4);T=beta/3
for i in range(3):T[2*i+2:2*i+4,2*i:2*i+2]=s.eye(2)/3
b=s.Matrix.hstack(*[T**i*s.eye(8)[:,0] for i in range(8)]);R=q.inv()*s.diag(*[P**14]*4);Ri=R.inv();bi=b.inv()
u=s.Matrix([[1,4,'4994/243','3661/729','418366/59049','4029958/177147','115597610/14348907','129140108/4782969'],[0,1,'56/3','4130/243','8735/729','178552/59049','632990/59049','287189225/14348907'],[0,0,1,'26/3','6559/243','16459/729','310582/19683','33164/2187'],[0,0,0,1,'70/3','4912/243','3965/243','338203/19683'],[0,0,0,0,1,'14/3','320/81','16483/729'],[0,0,0,0,0,1,'71/3','797/81'],[0,0,0,0,0,0,1,0],[0,0,0,0,0,0,0,1]])
def v3(x):
 x=s.Rational(x);a,d=abs(int(x.p)),int(x.q);n=0
 if not a:return 999
 while a%3==0:a//=3;n+=1
 while d%3==0:d//=3;n-=1
 return n
def res(x,m=3):
 x=s.Rational(x);return int(x.p)*pow(int(x.q),-1,m)%m
base=[s.eye(2),P,s.Matrix([[3,0],[0,0]]),s.Matrix([[0,9],[0,0]])]
def elim(cols,rows):
 for r in rows:
  if not cols:continue
  p=min(range(len(cols)),key=lambda i:v3(cols[i][r]))
  if not cols[p][r]:continue
  c=cols.pop(p);cols=[z-c*z[r]/c[r] for z in cols]
 return cols
h=s.eye(8)
for i in range(7):
 a,c=divmod(i,2);l,d=divmod(i+1,2);cols=[s.Matrix(list(Q[a].inv()*z*Q[l])) for z in base];up=[2*aa+cc for aa,cc in product(range(2),repeat=2) if 2*a+aa<2*l+cc];cols=elim(cols,[p for p in range(4) if p not in up]);p=2*c+d;z=min(cols,key=lambda z:v3(z[p]));z=z*u[i,i+1]/z[p];h[2*a:2*a+2,2*l:2*l+2]+=s.Matrix(2,2,list(z))
w=h.inv()*u;j0=Ri*w*bi;assert all(w[i,i+1]==0 for i in range(7))
# Solve affine Z_(3) lattice conditions M x+c integral, exact full basis.
def cut(M,c):
 n=M.cols;x=s.zeros(n,1);L=s.eye(n);index=0
 for r in range(M.rows):
  a=(M[r,:]*L);d=(M[r,:]*x)[0]+c[r];p=min(range(n),key=lambda k:v3(a[k]));v=v3(a[p]);
  if v>=0:
   if v3(d)<0:return None
   continue
  if v3(d)<v:return None
  col=L[:,p];x=x-col*d/a[p]
  for k in range(n):
   if k!=p:L[:,k]=L[:,k]-col*a[k]/a[p]
  L[:,p]=col*3**(-v);index-=v
 assert all(v3(z)>=0 for z in M*x+c) and all(v3(z)>=0 for z in M*L)
 assert all(v3(z)>=0 for z in x) and all(v3(z)>=0 for z in L)
 assert v3(L.det())==index
 return x,L,index
# For fixed lower rows of V, use saturated row-space quotient.
def quotient_rows(tail,n=8):
 if tail.rows==0:return s.eye(n)
 # Column operations over Z_(3), row operations over Q3, to move tail span to first r coords.
 A=tail.copy();C=s.eye(n);r=tail.rows
 for i in range(r):
  p,k=min(((p,k) for p in range(i,r) for k in range(i,n)),key=lambda pk:v3(A[pk]));assert A[p,k]
  A.row_swap(i,p);A.col_swap(i,k);C.col_swap(i,k)
  for j in range(i+1,n):
   z=A[i,j]/A[i,i];assert v3(z)>=0;A[:,j]-=z*A[:,i];C[:,j]-=z*C[:,i]
  for j in range(i+1,r):A[j,:]-=A[j,i]/A[i,i]*A[i,:]
 assert v3(C.det())==0 and all(v3(z)>=0 for z in C)
 D=C[:,r:];assert tail*D==s.zeros(r,n-r)
 return D
# Verify row membership and original inverse, with explicit lifts.
def root_free_lift(V):
 Z=s.eye(8)
 if v3(V.det())!=0 or any(v3(V[7,j]-int(j==7))<20 for j in range(8)):return None
 for i in range(7):
  tail=V[i+2:,:];D=quotient_rows(tail);a=V[i,:]*D
  if any(v3(z)<0 for z in a):return None
  # Complete D by integral pivot columns via transpose-style elimination (solve a congruence modulo integral row).
  if tail.rows:
   # choose coordinate chart C from row nullspace via independent saturated complement; use rref on rational tail then solve integrality via cut.
   # A direct solution: find integral row y with y D=a using a unit maximal minor of D.
   from itertools import combinations
   inds=next(idx for idx in combinations(range(8),D.cols) if v3(D[list(idx),:].det())==0)
   y=s.zeros(1,8);v=a*D[list(inds),:].inv()
   for k,t in enumerate(inds):y[t]=v[k]
   diff=y-V[i,:]; coeff=tail.T.gauss_jordan_solve(diff.T)[0]
   for k,z in enumerate(coeff):Z[i,i+2+k]=z
  else:
   assert all(v3(z)>=0 for z in V[i,:])
 K=Z*V;assert all(v3(z)>=0 for z in K) and v3(K.det())==0 and all(v3(K[7,j]-int(j==7))>=20 for j in range(8));return Z.inv(),K
assert root_free_lift(w) is not None
# Fixed bottom six ORIGINAL rows of j. Top block row affine parameterization.
J=j0.copy();J[:2,:]=s.zeros(2,8);J[:2,:2]=2*s.eye(2)
Gs=[]
for col,k in product(range(4),range(4)):
 G=s.zeros(8);G[:2,2*col:2*col+2]=base[k]*(3 if col==0 and k==0 else 1);Gs.append(G)
V=R*J*b;Ds=[quotient_rows(V[i+2:,:]) for i in (0,1)];VG=[R*g*b for g in Gs]
c=s.Matrix([z for i,D in enumerate(Ds) for z in V[i,:]*D]);M=s.Matrix.hstack(*[s.Matrix([z for i,D in enumerate(Ds) for z in g[i,:]*D]) for g in VG]);sol=cut(M,c);assert sol is not None
x,L,idx=sol;J=J+sum((a*g for a,g in zip(x,Gs)),s.zeros(8));G2=[sum((L[k,i]*g for k,g in enumerate(Gs)),s.zeros(8)) for i in range(16)]
print('top block affine index',idx,'quotient ranks',[D.cols for D in Ds],flush=True)
# R341 scalar character lookup, no general dense cuspidal matrices.
def kmul(a,b):return ((a[0]*b[0]-3*a[1]*b[1])%9,(a[0]*b[1]+a[1]*b[0]+3*a[1]*b[1])%9)
H={(1,0)}
for g in [(8,0),(4,7),(7,0)]:
 p=(1,0);ps=[]
 for _ in range(18):ps.append(p);p=kmul(p,g)
 H={kmul(h,p) for h in H for p in ps}
chi={kmul(h,v):i for i,v in enumerate([(1,0),(1,6),(1,3)]) for h in H};assert len(chi)==54
xx=s.Symbol('x');pol=xx**2-3*xx+3
# Project just seven free top-row finite C,D labels; original lift remains.
labels=[(0,2*i) for i in range(1,4)]+[(1,2*i) for i in range(4)]
def residues(g):return s.Matrix([res(g[i,j]) for i,j in labels])
F=s.Matrix.hstack(*map(residues,G2));rows={};ker=[]
for k in range(16):
 y=F[:,k];v=s.eye(16)[:,k]
 for p,(r,t) in sorted(rows.items()):
  a=int(y[p]);y=(y-a*r).applyfunc(lambda z:z%3);v-=a*t
 if any(y):
  p=next(i for i,a in enumerate(y) if a);a=int(y[p]);rows[p]=((a*y).applyfunc(lambda z:z%3),a*v)
 else:ker.append(v)
rank=len(rows);print('top residue rank',rank,flush=True)
# Kernel lattice generated by these exact vectors and 3 times each pivot vector.
ker += [3*t for r,t in rows.values()];assert len(ker)==16
assert all(not any((F*t).applyfunc(lambda z:z%3)) for t in ker)
assert v3(s.Matrix.hstack(*ker).det())==rank
kg=[sum((a*g for a,g in zip(t,G2)),s.zeros(8)) for t in ker]
# Use exact modular arithmetic for phase evaluation. All relevant arguments are integral.
import numpy as np
from itertools import permutations
arr=lambda g:np.array([[res(z,27) for z in g.row(i)] for i in range(g.rows)],dtype=np.int64)
Jm=arr(J); Gm=[arr(g) for g in G2]; Km=[arr(g) for g in kg]; Bm=np.array((9*beta).tolist(),dtype=np.int64)
perms=[(p,(-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))) for p in permutations(range(4))]
def inv27(k):
 a=np.concatenate((k.copy(),np.eye(8,dtype=np.int64)),axis=1)
 for i in range(8):
  p=next(p for p in range(i,8) if int(a[p,i])%3);a[[i,p]]=a[[p,i]];a[i]=a[i]*pow(int(a[i,i]),-1,27)%27
  for p in range(8):
   if p!=i:a[p]=(a[p]-a[p,i]*a[i])%27
 return a[:,8:]
def detphase(C,D):
 a=b=0
 for p,sgn in perms:
  t=(sgn,0)
  for i,j in enumerate(p):t=kmul(t,(int(C[i,j]),int(D[i,j])))
  a+=t[0];b+=t[1]
 return chi[a%9,b%9]
counts=Counter();checks=0
lifts=[arr(sum((a*g for a,g in zip(t,G2)),s.zeros(8))) for r,t in rows.values()]
for co in product(range(3),repeat=rank):
 j=(Jm+sum((a*g for a,g in zip(co,lifts)),np.zeros((8,8),dtype=np.int64)))%27
 C=j[::2,::2]%3;D=j[1::2,::2]%3;k=np.zeros((8,8),dtype=np.int64);k[::2,::2]=C;k[::2,1::2]=-3*D;k[1::2,::2]=D;k[1::2,1::2]=C+3*D;ki=inv27(k%27);Y=(ki@j-np.eye(8,dtype=np.int64))%27
 assert not np.any(Y%3) and not np.any(Y[::2,1::2]%9)
 t=[int(np.trace(Bm@ki@g))%27 for g in Km];assert all(z%9==0 for z in t)
 if any(t):counts['cancelled']+=1;continue
 tr=int(np.trace(Bm@Y))%27;assert tr%9==0
 d=C@np.diag([-1,1,-1,1]);p=(detphase(C,D)+tr//9+sum(d[i,i+1] for i in range(3)))%3;counts[int(p)]+=1;checks+=1
print('residue counts',dict(counts),'constant fibres',checks,'cell mass relative',f'3^-{idx+rank}',flush=True)
assert sum(counts.values())==3**rank
# Exact independent original inverse on a few admitted residue representatives.
for co in list(product(range(3),repeat=rank))[::121]:
 y=sum((a*t for a,(r,t) in zip(co,rows.values())),s.zeros(16,1));j=J+sum((a*g for a,g in zip(y,G2)),s.zeros(8));assert root_free_lift(R*j*b) is not None
