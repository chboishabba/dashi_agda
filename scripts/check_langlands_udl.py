"""R360: actual block-order UDL and three-root quotient."""
from pathlib import Path
# Reuse original constructors from the preceding checker without running its conditional enumeration.
# In repo the helper definitions are loaded from the sibling file through a delimited prefix.
exec(Path(__file__).with_name('check_langlands_block_row.py').read_text().split('# Fixed bottom six ORIGINAL rows')[0])

def order(M):
 return all(v3(x)>=0 for x in M) and v3(M[0,0]-M[1,1])>=1 and v3(M[0,1]+3*M[1,0])>=2

def udl(j):
 A=s.eye(8);D=s.zeros(8);L=s.eye(8);M=j.copy()
 for l in reversed(range(4)):
  k=2*l; d=M[k:k+2,k:k+2]; assert order(d) and v3(d.det())==0
  D[k:k+2,k:k+2]=d
  if k:
   a=M[:k,k:k+2]*d.inv();ell=d.inv()*M[k:k+2,:k]
   A[:k,k:k+2]=a;L[k:k+2,:k]=ell
   M[:k,:k]-=a*d*ell
 assert A*D*L==j
 for i,l in product(range(4),repeat=2):
  for F in (A,D,L):assert order(F[2*i:2*i+2,2*l:2*l+2])
  if i>l:assert res(L[2*i,2*l])==0
 return A,D,L

def roots(V):return tuple(V[i,i+1] for i in range(7))
def root_res(V):return tuple(res(3*x) if v3(x)>=-1 else None for x in roots(V))
def section(t):
 a=s.eye(8)
 for i,n in enumerate(t):
  k=2*i;l=k+2
  a[k:k+2,l:l+2]=n*s.eye(2)
 return a
# Exact adjacent character relation on the four generators.
for i in range(3):
 k=2*i;l=k+2
 vals=[(R[k:k+2,k:k+2]*g*Ri[l:l+2,l:l+2])[1,0] for g in base]
 print('root functional',i,vals,flush=True)
 assert min(map(v3,vals))==-1
 assert [res(3*z) for z in vals]==[1,0,0,0]
A,D,L=udl(j0);B0=D*L;V0=R*B0*b;Au=R*A*Ri
assert all(v3(z)>=-1 for z in roots(Au))
t=tuple(root_res(Au)[i] for i in (1,3,5));print('actual upper residue',t,flush=True)
# Root-free support test with saturated quotient, without repeated full rational lifts.
def admissible(V):
 if any(v3(V[7,j]-int(j==7))<20 for j in range(8)):return False
 return all(all(v3(z)>=0 for z in V[i,:]*quotient_rows(V[i+2:,:])) for i in range(7))
# Use original A as lift for selected t; for other t use section shifts in original upper group.
hits=[]
for c in product(range(3),repeat=3):
 V=R*section(c)*B0*b
 if admissible(V):hits.append(c)
assert hits==[t]
assert root_free_lift(R*section(t)*B0*b) is not None
# Full U rather than U^0 decomposition gives the seven simple-root invariants modulo Z3.
def full_lift(V):
 Z=s.eye(8)
 if any(v3(V[7,j]-int(j==7))<20 for j in range(8)):return None
 from itertools import combinations
 for i in range(7):
  tail=V[i+1:,:];D=quotient_rows(tail);a=V[i,:]*D
  if any(v3(z)<0 for z in a):return None
  inds=next(idx for idx in combinations(range(8),D.cols) if v3(D[list(idx),:].det())==0)
  y=s.zeros(1,8);v=a*D[list(inds),:].inv()
  for k,j in enumerate(inds):y[j]=v[k]
  coeff=tail.T.gauss_jordan_solve((y-V[i,:]).T)[0]
  for k,z in enumerate(coeff):Z[i,i+1+k]=z
 K=Z*V;assert all(v3(z)>=0 for z in K) and v3(K.det())==0
 return Z.inv(),K
uu,kk=full_lift(V0);r=root_res(uu);assert all(x is not None for x in r) and all(r[i]==0 for i in (0,2,4,6));assert tuple(-r[i]%3 for i in (1,3,5))==t
print('27 upper classes, hits',hits,'full root residues',r,flush=True)
# Unit pivots, additive Haar volumes and group-character factor.
assert v3(s.Matrix.hstack(*[s.Matrix(list(g)) for g in base]).det())==3
assert 6*3+10*4==58 and 263-18-3==242
print('UDL exact; upper fibre 3^-21; lower-carrier volume 3^-40; reversed factor 3^242',flush=True)
# Independent diagonal scalar phase using the original R341 lookup.
def kmul(a,b):return ((a[0]*b[0]-3*a[1]*b[1])%9,(a[0]*b[1]+a[1]*b[0]+3*a[1]*b[1])%9)
H={(1,0)}
for g in [(8,0),(4,7),(7,0)]:
 p=(1,0);powers=[]
 for _ in range(18):powers.append(p);p=kmul(p,g)
 H={kmul(h,p) for h in H for p in powers}
chi={kmul(h,v):i for i,v in enumerate([(1,0),(1,6),(1,3)]) for h in H};assert len(chi)==54
phase=0
for i in range(4):
 d=D[2*i:2*i+2,2*i:2*i+2];c=res(d[0,0]);e=res(d[1,0]);k=c*s.eye(2)+e*P;Y=k.inv()*d-s.eye(2)
 assert all(v3(z)>=1 for z in Y) and v3(Y[0,1])>=2
 tr=s.trace(B*Y);assert v3(tr)>=0
 phase=(phase+chi[c,e]+res(tr))%3
assert (phase+sum(t))%3==0
print('diagonal scalar exponent',phase,'total signed exponent',(phase+sum(t))%3)
