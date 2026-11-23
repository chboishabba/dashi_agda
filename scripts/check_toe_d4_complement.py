import numpy as np
import sympy as sp
from toe_cyclotomic_operator import compile_shape
from toe_cyclotomic_hom_batch import apply_batch
from toe_cyclotomic_butterfly import root
import check_toe_atlas_mirror as M
# Same signed block recipe and order as jfine_3b_linear_multiplicity_d4_repair.
COUNT={'A1':23,'A2':5,'B1':13,'B2':13,'E':18}
r=[];s=[]
for name,rv,sv in [('A1',1,1),('A2',1,-1),('B1',-1,1),('B2',-1,-1)]:
 for _ in range(COUNT[name]):
  i=len(r);r.append((i,rv));s.append((i,sv))
for _ in range(COUNT['E']):
 i=len(r);r.extend([(i+1,1),(i,-1)]);s.extend([(i,1),(i+1,-1)])
def mat(p):
 a=sp.zeros(len(p));
 for i,(j,k) in enumerate(p):a[j,i]=k
 return a
R,S=mat(r),mat(s); I=sp.eye(90)
assert R**4==S**2==I and S*R*S==R**3
assert [sp.trace(t) for t in [I,R**2,R,S,R*S]]==[90,18,2,18,18]
def channel(v,p,adj=False):
 if sorted(j for j,k in p)!=list(range(v.shape[-1])) or any(k not in (-1,1) for j,k in p):raise ValueError('signed permutation')
 out=np.zeros_like(v)
 for i,(j,k) in enumerate(p):
  if adj:out[:,:,i]=k*v[:,:,j]
  else:out[:,:,j]=k*v[:,:,i]
 return out
A=M.inv(M.Pa)@M.r@M.Pa%3; B=M.inv(M.Pa)@M.m@M.Pa%3
records={}
for phase in (1,2):
 for name,G,lam,g in [('r',A,1,[1,0,27]),('s',B,2,[1,0,1])]:
  records[name,phase]=dict(compile_shape(G,lam,phase),scalar=g)
def act(state,name,twist=0,adj=False):
 phase,v,den=state; target=phase if name=='r' else 3-phase
 rec=records[name,target if adj else phase]; p=r if name=='r' else s
 h,d=apply_batch(rec,v,adjoint=adj); h=channel(h,p,adj=adj)
 if twist:
  h=np.stack(root(tuple(h),twist)); h=np.stack(root(tuple(h),-twist))
 return target,h,den*d
def same(a,b):return a[0]==b[0] and np.array_equal(a[1]*b[2],b[1]*a[2])
rng=np.random.default_rng(26); v=rng.integers(-2,3,(2,729,90)).astype(object)
for phase in (1,2):
 x=(phase,v,1); y=act(x,'r'); assert same(act(y,'r',adj=True),x)
 z=act(x,'s'); assert same(act(z,'s'),x)
 r2=act(y,'r'); r3=act(r2,'r'); assert same(act(r3,'r'),x)
 assert same(act(act(z,'r'),'s'),r3)
 assert same(act(x,'r',twist=1),y)
 print('PASS phase',phase,'full nontrivial 65610 D4 relations, adjoint, gauge cancellation',flush=True)
z=sp.Symbol('z'); red=lambda f:sp.rem(sp.expand(f),z*z+z+1,z)
for i in range(3):
 for j in range(3):assert red(z**(i+j)*z**((-i-j)%3))==1
X=np.array(list(__import__('itertools').product(range(3),repeat=6))); V=A[6:,:6]; counts=np.bincount(np.sum((X@V)*X,axis=1)%3,minlength=3)
tr=red(sum(int(c)*z**i for i,c in enumerate(counts))/27)
assert tr in (-1,1)
assert sp.trace(R**2)==18
print('trace counts',counts.tolist(),'ATLAS Fourier trace',tr,'tensor C4 trace',[65610,2*tr,18,2*tr],flush=True)
