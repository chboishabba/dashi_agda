"""Exact rational SU(2) surface inequality fixtures; no Gibbs integration."""
from fractions import Fraction as Q
from random import Random
from itertools import product, combinations
from collections import Counter
import sympy as s
rng=Random(20261120)
I=(Q(1),Q(0),Q(0),Q(0))
def mul(q,r):
 a,b,c,d=q;e,f,g,h=r
 return (a*e-b*f-c*g-d*h,a*f+b*e+c*h-d*g,a*g-b*h+c*e+d*f,a*h+b*g-c*f+ d*e)
def inv(q): return (q[0],-q[1],-q[2],-q[3])
def hol(xs):
 z=I
 for v in xs:z=mul(z,v)
 return z
def deficit(q):return 1-q[0]
V=[tuple(Q(sign if i==j else 0) for i in range(4)) for j in range(4) for sign in (-1,1)]+[tuple(Q(a,2) for a in t) for t in product((-1,1),repeat=4)]
for b in (1,2,3,4,8,13):
 for case in range(20):
  H={(x,y):rng.choice(V) for x in range(b) for y in range(b+1)}
  W={(x,y):rng.choice(V) for x in range(b+1) for y in range(b)}
  fine=sum(deficit(hol([H[x,y],W[x+1,y],inv(H[x,y+1]),inv(W[x,y])])) for x,y in product(range(b),repeat=2))
  coarse=hol([H[x,0] for x in range(b)]+[W[b,y] for y in range(b)]+[inv(H[x,b]) for x in reversed(range(b))]+[inv(W[0,y]) for y in reversed(range(b))])
  assert deficit(coarse)<=b*b*fine
for M,b in ((2,2),(3,2),(2,3),(2,13)):
 L=M*b; count=Counter()
 for x in product(range(M),repeat=4):
  for i,j in combinations(range(4),2):
   for a,c in product(range(b),repeat=2):
    y=[b*v for v in x];y[i]+=a;y[j]+=c
    count[tuple(v%L for v in y),i,j]+=1
 assert len(count)==6*M**4*b*b and max(count.values())==1
for b in (2,4,8,16,32):
 t=Q(1,b*b);q=((1-t*t)/(1+t*t),2*t/(1+t*t),Q(0),Q(0))
 # Abelian open patch: H=I, W(x,y)=q^x, every fine plaquette q.
 coarse=hol([q]*(b*b))
 assert deficit(q)==2/(b**4+Q(1))
 assert deficit(coarse)>1
 assert deficit(coarse)<=b*b*b*b*deficit(q)
B, beta, eps, C=s.symbols('B beta eps C', positive=True)
assert s.simplify(beta*eps/(96*B**2)-C*B**2/4-(beta*eps-24*C*B**4)/(96*B**2))==0
print('PASS: 120 noncommuting surface fixtures, 4 periodic incidence fixtures, 5 Abelian flux controls, 1 symbolic rate identity')
