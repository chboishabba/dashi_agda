import numpy as np, hashlib, json
Crows="010000000000\n200000000000\n000100000000\n002000000000\n000001000000\n000020000000\n000000010000\n000000200000\n000000000010\n000000000001\n000000002000\n000000000200"
Drows="001000000000\n112000000000\n202000000000\n000010000000\n121220000000\n000000100000\n000000001000\n000000000100\n000001000000\n000001121200\n011212110210\n011210201001"
Jrows='''002122102121
001121022112
120000021212
220000201221
110000221021
120000212120
200111002221
011012002111
112221110201
221102121020
122111120101
211220222020'''
def mat(s):return np.array([[int(c) for c in r] for r in s.splitlines()],dtype=np.int64)
for rows,want in [(Crows,'ddd4919ab560f78b065aa08e309bd047942cdb7bb52a1474da84d54d35a031c2'),(Drows,'433ba0f0373995b159859df00dd5a5005355fdbf8b59a31d651aeaf43ffcd15f')]:
 assert hashlib.sha256(('1     3    12    12\n'+rows+'\n').encode()).hexdigest()==want
C,D,J=map(mat,(Crows,Drows,Jrows)); I=np.eye(12,dtype=np.int64)
def power(A,n):
 R=I.copy()
 for _ in range(n): R=R@A%3
 return R
def word(w):
 R=I.copy(); d={'C':C,'D':D,'c':power(C,3),'d':power(D,2)}
 for t in w:R=R@d[t]%3
 return R
def eq(a,b):return np.array_equal(a%3,b%3)
def rank(A):
 A=A.copy()%3;k=0
 for c in range(A.shape[1]):
  p=next((i for i in range(k,len(A)) if A[i,c]),None)
  if p is None:continue
  A[[k,p]]=A[[p,k]];A[k]=A[k]*A[k,c]%3
  for i in range(len(A)):
   if i!=k:A[i]=(A[i]-A[i,c]*A[k])%3
  k+=1
 return k
def independent(vs):
 out=[]
 for v in vs:
  if rank(np.array(out+[v]))>len(out):out.append(v)
 return out
def basis(J):
 work=list(I.copy());es=[];fs=[]
 while work:
  v=work[0];i=next(i for i,w in enumerate(work[1:],1) if v@J@w%3);w=work[i]*(v@J@work[i]%3)%3
  work=independent([(u-(u@J@w)*v+(u@J@v)*w)%3 for k,u in enumerate(work[1:],1) if k!=i]);es.append(v);fs.append(w)
 return np.array(es+fs).T
m=power(word('CDCDCDCDCDCdCd'),5);g=word('CdCdCDCd');gi=word(''.join({'C':'c','c':'C','D':'d','d':'D'}[t] for t in reversed('CdCdCDCd')));r=m@g@m@gi%3
assert eq(m@m,I) and eq(m.T@J@m,-J) and eq(r@r,-I) and eq(m@r@m,power(r,3));assert rank(J)==12
P=basis(J);L=P[:,:6];M=P[:,6:];plus=np.array(independent(list((I+m).T%3))).T;minus=np.array(independent(list((I-m).T%3))).T
assert plus.shape==minus.shape==(12,6);assert eq(plus.T@J@plus,0*I[:6,:6]) and eq(minus.T@J@minus,0*I[:6,:6]);assert rank(np.column_stack((plus,minus)))==12
print('source ranks',rank(np.column_stack((L,m@L))),rank(np.column_stack((M,m@M))), 'mirror adapted',rank(np.column_stack((plus,m@plus))),rank(np.column_stack((minus,m@minus))), 'rotation on mirror eigenspace',rank(np.column_stack((plus,r@plus))))
import sympy as sp
from itertools import product
def inv(A):
 return np.array(sp.Matrix(A.tolist()).inv_mod(3).tolist(),dtype=np.int64)
B=plus.T@J@minus%3;Pa=np.column_stack((plus,minus@inv(B)%3));Js=np.block([[np.zeros((6,6),dtype=np.int64),np.eye(6,dtype=np.int64)],[-np.eye(6,dtype=np.int64),np.zeros((6,6),dtype=np.int64)]])
assert eq(Pa.T@J@Pa,Js)
A=inv(Pa)@m@Pa%3;assert eq(A,np.diag([1]*6+[-1]*6))
Coc=np.zeros((12,12),dtype=np.int64);Coc[6:,:6]=np.eye(6,dtype=np.int64)
for name,Q in [('original',P),('adapted',Pa)]:
 A=inv(Q)@m@Q%3;E=(A.T@Coc@A+Coc)%3
 assert eq(E,E.T) and eq(2*(E+E.T),E)
 assert eq(A.T@E@A,E)
 print(name,'quadratic defect rank',rank(E),'modulation block rank',rank(A[:6,6:]))
count=0
for x in product(range(3),repeat=6):
 for phase in (1,2):
  for k in range(6):
   assert phase*x[k]%3==((-phase)*(-x[k]))%3;count+=1
print('adapted modulation exponent equalities',count)
print('PASS source hash, D4, polarizations, cocycle, paired phases')
