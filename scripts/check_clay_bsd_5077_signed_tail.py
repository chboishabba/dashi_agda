"""Exact selected rank-three sign and localization controls for 5077.a1."""
from fractions import Fraction as Q
from math import factorial
import sympy as sp
checks=0
def check(ok,msg):
 global checks
 if not ok:raise AssertionError(msg)
 checks+=1
N=5077;M=550
# y^2+y=x^3-7x+6
ap={}
def trace(p):
 c=[0]*p
 for y in range(p):c[(y*y+y)%p]+=1
 return p-sum(c[(x*x*x-7*x+6)%p] for x in range(p))
for l in sp.primerange(2,M+1):ap[int(l)]=trace(int(l))
def coeff(n):
 a=1
 for p,e in sp.factorint(n).items():
  x,y=1,ap[p]
  for _ in range(1,e):x,y=y,ap[p]*y-p*x
  a*=y
 return a
cs=[coeff(n) for n in range(1,M+1)]
R=Q(916,1000)
T0=2*R**M*((M+1)/(1-R)+R/(1-R)**2)
T1=2*R**(M-1)*(M*(M+1)/(1-R)+(2*M+1)*R/(1-R)**2+R*(1+R)/(1-R)**3)
S=10**25;den=10000
# Fixed-point outward-rounded interval Horner, exact integer arithmetic.
def enclosure(c,a,b):
 lo=hi=c[-1]*S
 for z in reversed(c[:-1]):
  v=lo*a,lo*b,hi*a,hi*b
  lo=min(v)//den+z*S
  hi=-((-max(v))//den)+z*S
 return Q(lo,S),Q(hi,S)
dc=[i*a for i,a in enumerate(cs) if i]
for j in range(0,4000):check(enclosure(dc,j,j+1)[1]+T1<0,'negative derivative')
for j in range(4000,9000):check(enclosure(cs,j,j+1)[1]+T0<0,'negative middle')
for j in range(9000,9160):check(enclosure(dc,j,j+1)[0]-T1>0,'positive terminal derivative')
# 0.9 < exp(-2pi/sqrt5077) < 0.916. Lower bound e^-x >=1-x.
check(Q(71)**2<N and 1-Q(44,7*71)>Q(9,10),'lower q bound')
x=Q(628,7130) # sqrt5077 <71.3, pi>3.14
check(Q(713,10)**2>N and sum(x**j/factorial(j) for j in range(5))>1/R,'upper q bound')
b2,b4,b6,b8=0,-14,25,-49
D=-b2*b2*b8-8*b4**3-27*b6*b6+9*b2*b4*b6
check(D==N and (-24*b4)%N!=0,'prime multiplicative discriminant')
check(trace(N)==-1,'negative root sign')
# exact local group law
O=None
def add(P,Qp,l):
 if P is None:return Qp
 if Qp is None:return P
 x,y=P;u,v=Qp
 if x==u:
  if (y+v+1)%l==0:return None
  s=(3*x*x-7)*pow((2*y+1)%l,-1,l)%l
 else:s=(v-y)*pow((u-x)%l,-1,l)%l
 z=(s*s-x-u)%l
 return z,(-1-y+s*(x-z))%l
def mul(n,P,l):
 R=None
 while n:
  if n%2:R=add(R,P,l)
  P=add(P,P,l);n//=2
 return R
pts=[(0,2),(1,0),(2,0)]
mat=[]
for l in (71,401,631):
 order=l+1-trace(l)
 print(l,order,flush=True)
 check(order%5==0 and order%25!=0 and (l-1)%5==0,'Kolyvagin prime and exact single five factor')
 row=[mul(order//5,P,l) for P in pts]
 G=next(P for P in row if P is not None)
 check(mul(5,G,l) is None,'order5')
 a=[next(k for k in range(5) if mul(k,G,l)==P) for P in row]
 print(a,flush=True);mat.append(a)
check(sp.Matrix(mat).det()%5!=0,'independent mod5')
check((3+1-trace(3))%5!=0,'no five torsion')
print('tail bounds',float(T0),float(T1),f'{checks}/{checks} PASS')
