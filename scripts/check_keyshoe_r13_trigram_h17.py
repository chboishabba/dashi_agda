from itertools import product, permutations
from collections import Counter
import sympy as sp
# DASHI candidate orbit of the screenshot-transcribed NPW triangle.
# JQZ is only a hypothetical letter-slot comparison, NOT a port/letter weld.
bodies='GH IJ KL MN OP QR ST UV WX YZ AB CD EF'.split()
slots={l:((i-3)%13,s) for i,b in enumerate(bodies) for s,l in enumerate(b)}
L=list(slots.values()); G=list(product(range(13),[1,-1],range(2)))
def act(g,x):
 k,e,f=g; j,s=x; return ((k+e*j)%13,s^f)
def orbit(xs):return {tuple(act(g,x) for x in xs) for g in G}
def stats(R):
 out=[]
 for i in range(3):
  d=Counter(tuple(x[j] for j in range(3) if j!=i) for x in R)
  out.append((len(d),dict(Counter(d.values()))))
 return out
T=sp.symbols('t'); p=sp.Poly(T**3-T-1,T,modulus=3)
def field(x):
 j,s=x; q=sp.Poly((-1)**s*T**j,T,modulus=3).rem(p);return tuple(int(q.nth(i))%3 for i in range(3))
assert len(set(map(field,L)))==26
for name in ['NPW','JQZ']:
 xs=tuple(slots[l] for l in name); R=orbit(xs); U={v for x in R for v in permutations(x)}
 print(name,xs,'field',list(map(field,xs)),'det',sp.Matrix(list(map(field,xs))).det()%3,'ordered',len(R),stats(R),'unordered',len(U),stats(U))
 assert all(tuple(act(g,x) for x in v) in R for g in G for v in R)
 for v in R:
  for i in range(3):
   observed=[j for j in range(3) if j!=i]
   a,b=observed; candidates=[g for g in G if act(g,xs[a])==v[a] and act(g,xs[b])==v[b]]
   assert len(candidates)==1 and act(candidates[0],xs[i])==v[i]
 print('determinant histogram',Counter(int(sp.Matrix(list(map(field,x))).det()%3) for x in R))
print('PASS: signed chart, orbit closure and all ordered pair round trips')
