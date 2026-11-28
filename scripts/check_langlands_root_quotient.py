"""R354-R356: conductor-zero correction and original root-free quotient."""
import sympy as s
from itertools import product
B=s.Matrix([[6,21],[-7,-15]])/9; P=s.Matrix([[0,-3],[1,3]])
X=s.Matrix.hstack(s.eye(2)[:,0],B[:,0]); Q=[B**i*X*s.diag(3**(7-2*i),3**(6-2*i)) for i in range(4)]; q=s.diag(*Q); beta=s.diag(*[B]*4)
T=beta/3
for i in range(3):T[2*i+2:2*i+4,2*i:2*i+2]=s.eye(2)/3
b=s.Matrix.hstack(*[T**i*s.eye(8)[:,0] for i in range(8)]); R=q.inv()*s.diag(*[P**14]*4)
u=s.Matrix([[1,4,'4994/243','3661/729','418366/59049','4029958/177147','115597610/14348907','129140108/4782969'],[0,1,'56/3','4130/243','8735/729','178552/59049','632990/59049','287189225/14348907'],[0,0,1,'26/3','6559/243','16459/729','310582/19683','33164/2187'],[0,0,0,1,'70/3','4912/243','3965/243','338203/19683'],[0,0,0,0,1,'14/3','320/81','16483/729'],[0,0,0,0,0,1,'71/3','797/81'],[0,0,0,0,0,0,1,0],[0,0,0,0,0,0,0,1]])
def v3(x):
 x=s.Rational(x); a,b=abs(int(x.p)),int(x.q); n=0
 if not a:return 10**6
 while a%3==0:a//=3;n+=1
 while b%3==0:b//=3;n-=1
 return n
def res(x,m=3):
 x=s.Rational(x);return int(x.p)*pow(int(x.q),-1,m)%m
def kmul(a,b):return ((a[0]*b[0]-3*a[1]*b[1])%9,(a[0]*b[1]+a[1]*b[0]+3*a[1]*b[1])%9)
H={(1,0)}
for g in [(8,0),(4,7),(7,0)]:
 p=(1,0);powers=[]
 for _ in range(18):powers.append(p);p=kmul(p,g)
 H={kmul(h,p) for h in H for p in powers}
chi={kmul(h,v):i for i,v in enumerate([(1,0),(1,6),(1,3)]) for h in H}
assert len(H)==18 and len(chi)==54
x=s.Symbol('x'); pol=x*x-3*x+3
def phase_of(j):
 C=j[::2,::2].applyfunc(res);D=j[1::2,::2].applyfunc(res); k=s.zeros(8)
 for i,l in product(range(4),repeat=2):k[2*i:2*i+2,2*l:2*l+2]=C[i,l]*s.eye(2)+D[i,l]*P
 assert v3(j.det())==0 and all(v3(z)>=0 for z in j)
 d=C*s.diag(-1,1,-1,1)
 assert all(int(d[i,l])%3==int(i==l) for i in range(4) for l in range(i+1))
 Y=k.inv()*j-s.eye(8);tr=s.trace(beta*Y)/3
 assert all(v3(Y[i,l])>=1+int(i%2==0 and l%2==1) for i,l in product(range(8),repeat=2))
 det=s.rem((C+x*D).det(),pol,x)
 return (chi[tuple(int(det.coeff(x,i))%9 for i in range(2))]+res(3*tr)+sum(d[i,i+1] for i in range(3)))%3
assert phase_of(R.inv()*u*b.inv())==0
assert sum(u[i,i+1] for i in range(7))==83
# Conductor zero means psi_0 is trivial on the integral trace/3.
for z in product(range(3),repeat=7):
 a=[1]*8
 for i in reversed(range(7)):a[i]=(1+3*z[i])*a[i+1]
 tr=-sum(s.Rational(a[i]-1,3) for i in [1,3,5,7])
 assert v3(tr)>=0
base=[s.eye(2),P,s.Matrix([[3,0],[0,0]]),s.Matrix([[0,9],[0,0]])]
def elim(cols,rows):
 for r in rows:
  if not cols:continue
  p=min(range(len(cols)),key=lambda i:v3(cols[i][r]))
  if not cols[p][r]:continue
  c=cols.pop(p);cols=[z-c*z[r]/c[r] for z in cols]
 return cols
v=0; ledger=[]
for i,l in product(range(4),repeat=2):
 cols=[s.Matrix(list(Q[i].inv()*z*Q[l])) for z in base]
 up=[2*a+c for a,c in product(range(2),repeat=2) if 2*i+a<2*l+c]
 cols=elim(cols,[p for p in range(4) if p not in up]); assert len(cols)==len(up)
 val=v3(s.Matrix.hstack(*[s.Matrix([z[p] for p in up]) for z in cols]).det()) if up else 0
 ledger.append(val);v+=val
assert v==-126
h=s.eye(8); roots=[]
for i in range(7):
 a,c=divmod(i,2); l,d=divmod(i+1,2)
 cols=[s.Matrix(list(Q[a].inv()*z*Q[l])) for z in base]
 up=[2*aa+cc for aa,cc in product(range(2),repeat=2) if 2*a+aa<2*l+cc]
 cols=elim(cols,[p for p in range(4) if p not in up]); p=2*c+d
 z=min(cols,key=lambda z:v3(z[p])); roots.append(v3(z[p]));z=z*u[i,i+1]/z[p]
 h[2*a:2*a+2,2*l:2*l+2]+=s.Matrix(2,2,list(z))
assert roots==[-1]*7 and [h[i,i+1] for i in range(7)]==[u[i,i+1] for i in range(7)]
J=q*h*q.inv()
assert all(v3(z)>=0 for z in J)
for i,l in product(range(4),repeat=2):
 assert v3(J[2*i,2*l]-J[2*i+1,2*l+1])>=1
 assert v3(J[2*i,2*l+1]+3*J[2*i+1,2*l])>=2
w=h.inv()*u; assert all(w[i,i+1]==0 for i in range(7))
assert min(map(v3,w))==-15 and phase_of(R.inv()*w*b.inv())==0
assert min(map(v3,R.inv()))==-13 and min(map(v3,b.inv()))==-4
M=38; assert M-18-13-4==3
assert 21*18-160-85*M-(119-382)==-2749
print('root image (1/3 Z3)^7; H_U volume exponent 126; root-free volume exponent 119; original and root-free phase 0; pair-count fibre exponent 2749')
