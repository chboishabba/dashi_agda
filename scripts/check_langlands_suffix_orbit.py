"""R364-R366: original stabilizer orbit and conditional signed next-suffix image."""
from pathlib import Path
exec(Path(__file__).with_name('check_langlands_block_row.py').read_text().split('# Solve affine Z_(3) lattice conditions')[0])
from fractions import Fraction as F
def val(x):
 if not x:return 999
 a,d=abs(x.numerator),x.denominator;n=0
 while a%3==0:a//=3;n+=1
 while d%3==0:d//=3;n-=1
 return n
def cutfast(M,c):
 n=M.cols; x=[F(0)]*n;L=[[F(int(i==j)) for i in range(n)] for j in range(n)];idx=0
 for r in range(M.rows):
  m=[F(z) for z in M.row(r)];a=[sum(y*z for y,z in zip(m,col)) for col in L];d=sum(y*z for y,z in zip(m,x))+F(c[r]);p=min(range(n),key=lambda k:val(a[k]));v=val(a[p]);
  if v>=0:
   if val(d)<0:return None
   continue
  if val(d)<v:return None
  col=L[p];x=[y-z*d/a[p] for y,z in zip(x,col)]
  for k in range(n):
   if k!=p and a[k]:L[k]=[y-z*a[k]/a[p] for y,z in zip(L[k],col)]
  L[p]=[z*3**(-v) for z in col];idx-=v
 return s.Matrix(x),s.Matrix(L).T,idx
# Original H_b: K=I+Y, last row increments divisible 3^20.
Gs=[]
for i,k in product(range(8),repeat=2):
 g=s.zeros(8);g[i,k]=3**20 if i==7 else 1;Gs.append(g)
def ordergate(g):
 return list(g)+[(g[2*i,2*l]-g[2*i+1,2*l+1])/3 for i,l in product(range(4),repeat=2)]+[(g[2*i,2*l+1]+3*g[2*i+1,2*l])/9 for i,l in product(range(4),repeat=2)]
M=s.Matrix.hstack(*[s.Matrix(ordergate(b*g*bi)) for g in Gs]);sol=cutfast(M,s.zeros(M.rows,1));x,L,idx=sol;print('stabilizer index',idx,flush=True)
assert idx==222
# rank/image volume of last 2 K rows in affine R362 gate coordinates. Work in integral row space y with last row divided by 3^20.
# 16 rows of L, exact lattice via p-adic row elimination of column generators.
def image_basis(M):
 cols=[M[:,i] for i in range(M.cols)];bas=[];vs=[]
 for r in range(M.rows):
  if not cols:break
  p=min(range(len(cols)),key=lambda i:v3(cols[i][r]));c=cols[p];
  if not c[r]:continue
  cols.pop(p);cols=[z-c*z[r]/c[r] for z in cols];bas.append(c);vs.append(v3(c[r]))
 return s.Matrix.hstack(*bas),vs
A,vs=image_basis(L[48:64,:]);print('stabilizer projection',vs,sum(vs),flush=True)
# Bottom gate on original j rows, parameterization same as R362
J=s.zeros(8);J[6:8,6:8]=s.eye(2);Bs=[]
for c,k in product(range(4),range(4)):
 G=s.zeros(8);G[6:8,2*c:2*c+2]=base[k]*(3 if k==0 else 1);Bs.append(G)
def gate(V,offset=False):return s.Matrix(list(V[6,:])+[(V[7,j]-int(offset and j==7))/3**20 for j in range(8)])
M2=s.Matrix.hstack(*[gate(R*g*b) for g in Bs]);sol=cutfast(M2,gate(R*J*b,True));x2,L2,idx2=sol;print('bottom gate idx',idx2,flush=True)
assert idx2==111
C=M2*L2;print('bottom gate image index',v3(C.det()),'rank',C.rank(),flush=True)
print('orbit inside gate',min(map(v3,C.inv()*A)), 'relative idx',v3((C.inv()*A).det()),flush=True)
assert v3(C.det())==51 and sum(vs)==61 and min(map(v3,C.inv()*A))>=0 and v3((C.inv()*A).det())==10
print('image residue first row',A[:7,:].applyfunc(res),flush=True)
assert not any(A[:7,:].applyfunc(res))
from collections import Counter
# Bottom of original j0 is already integral frame (e7,e8).
assert R[6:8,6:8]*j0[6:8,:]*b==s.eye(8)[6:8,:]
J=s.zeros(8);J[4:6,4:6]=2*s.eye(2);Gs=[]
for c,k in product(range(3),range(4)):
 G=s.zeros(8);G[4:6,2*c:2*c+2]=base[k]*(3 if k==0 else 1);Gs.append(G)
def gate(V):return list(V[4,:6])+list(V[5,:6])+[3*V[5,6]]
M=s.Matrix.hstack(*[s.Matrix(gate(R*g*b)) for g in Gs]);sol=cutfast(M,s.Matrix(gate(R*J*b)));assert sol is not None
x,L,idx=sol;J+=sum((a*g for a,g in zip(x,Gs)),s.zeros(8));Gs=[sum((L[k,i]*g for k,g in enumerate(Gs)),s.zeros(8)) for i in range(12)]
print('next block index',idx,'mass exponent',12+idx,flush=True)
def modimage(F):
 rows={};ker=[]
 for k in range(F.cols):
  y=F[:,k].applyfunc(res);v=s.eye(F.cols)[:,k]
  for p,(r,t) in sorted(rows.items()):a=int(y[p]);y=(y-a*r).applyfunc(lambda z:z%3);v-=a*t
  if any(y):
   p=next(i for i,a in enumerate(y) if a);a=int(y[p]);rows[p]=((a*y).applyfunc(lambda z:z%3),a*v)
  else:ker.append(v)
 ker += [3*t for r,t in rows.values()];return list(rows.values()),ker
# split by diagonal pi residue to linearize wild trace
F=s.Matrix([[res(g[5,4]) for g in Gs]]);rs,ks=modimage(F);print('diag pi residue rank',len(rs),flush=True)
# exact character lookup from R360
def kmul(a,b):return ((a[0]*b[0]-3*a[1]*b[1])%9,(a[0]*b[1]+a[1]*b[0]+3*a[1]*b[1])%9)
H={(1,0)}
for g in [(8,0),(4,7),(7,0)]:
 p=(1,0);powers=[]
 for _ in range(18):powers.append(p);p=kmul(p,g)
 H={kmul(h,p) for h in H for p in powers}
chi={kmul(h,v):i for i,v in enumerate([(1,0),(1,6),(1,3)]) for h in H};assert len(chi)==54
counts=Counter();ranks=[];byframe={}
for coeff in product(range(3),repeat=len(rs)):
 y=sum((a*t for a,(r,t) in zip(coeff,rs)),s.zeros(12,1));Jd=J+sum((a*g for a,g in zip(y,Gs)),s.zeros(8));Hgs=[sum((a*g for a,g in zip(t,Gs)),s.zeros(8)) for t in ks]
 d=Jd[4:6,4:6];cr=res(d[0,0]);dr=res(d[1,0]);k=cr*s.eye(2)+dr*P
 def obs(g,offset=False):
  V=R*g*b;dg=g[4:6,4:6];tr=s.trace(B*(k.inv()*dg-(s.eye(2) if offset else s.zeros(2))));assert v3(tr)>=0
  return s.Matrix([res(z) for z in list(V[4,:6])+list(V[5,:6])]+[res(tr-3*V[5,6])])
 a=obs(Jd,True);F=s.Matrix.hstack(*[obs(g) for g in Hgs]);rs2,ks2=modimage(F);rank=len(rs2);ranks.append(rank);print('phase image',dr,rank,flush=True)
 for co in product(range(3),repeat=rank):
  v=(a+sum((c*r for c,(r,t) in zip(co,rs2)),s.zeros(13,1))).applyfunc(lambda z:z%3)
  a0=list(v[:6]);a1=list(v[6:12]);primitive=any(a0[i]*a1[j]%3!=a0[j]*a1[i]%3 for i in range(6) for j in range(i+1,6))
  counts[int((v[12]+chi[cr,dr])%3) if primitive else 'nonprimitive']+=1
  if primitive:byframe.setdefault(tuple(a0+a1),Counter())[int((v[12]+chi[cr,dr])%3)]+=1
print('rank list',ranks,'counts',dict(counts),flush=True)
print('primitive frame labels',len(byframe),'phase distribution hist',Counter(tuple(c[i] for i in range(3)) for c in byframe.values()))
assert idx==12 and ranks==[4,4,4] and len(rs)==1
assert counts==Counter({'nonprimitive':135,0:36,1:36,2:36})
assert len(byframe)==12 and all(tuple(c[i] for i in range(3))==(3,3,3) for c in byframe.values())
