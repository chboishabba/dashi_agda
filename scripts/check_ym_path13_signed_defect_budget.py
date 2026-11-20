import sympy as s
from collections import Counter
from itertools import product
L=13; N=L**4; Z=(0,)*4
def walk(start,offset):
 x=list(start)
 for d,n in enumerate(offset):
  for _ in range(abs(n)):
   if n<0:x[d]-=1
   yield tuple(x),d
   if n>0:x[d]+=1
def shift(x,mu):return tuple(a+L*(k==mu) for k,a in enumerate(x))
m=Counter(); c=[Counter() for _ in range(4)]
for x in product(range(-6,7),repeat=4):
 m.update(walk(Z,x))
 for mu in range(4):c[mu].update(walk(x,shift(Z,mu)))
cols=[Counter() for _ in range(4)]
for mu in range(4):
 for i,src in enumerate([m,Counter({(shift(x,mu),d):v for (x,d),v in m.items()}),c[mu],Counter({e:N for e in walk(Z,shift(Z,mu))})]):
  for (x,d),v in src.items():cols[i][tuple(a%L for a in x),d]+=v
print([max(a.values()) for a in cols]); print(max((sum(a[k] for a in cols),k) for k in set().union(*cols)))
print([max(sum(a[k] for a in cols) for k in set().union(*cols) if k[1]==d) for d in range(4)])
def budget(e):
 x=222*e; j=x/(2-x); d=x/2; a=d+j; b=a+148*e; c=a+74*e; h=x+b
 weights=[a,b,c,h]
 row=(s.Rational(168,13)*(a+b)+13*(c+h))/13
 col=max(sum(w*S[k] for w,S in zip(weights,cols)) for k in set().union(*cols))/(13*N)
 return row,col,s.factor(N*row*col)
for e in [s.Rational(1,2048),s.Rational(1,65536),s.Rational(1,1048576)]:
 r,c,v=budget(e);print(e,r,c,v,float(v), 'relative ratio sq',float(v/s.Rational(57,169)))
