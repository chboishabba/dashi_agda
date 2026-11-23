#!/usr/bin/env python3
"""Native L4 original Wilson C3 source-coefficient audit; Q8 is diagnostic only."""
from itertools import product, combinations
from random import Random
from fractions import Fraction as Q
L=4
sites=tuple(product(range(4),repeat=4))
links=tuple((s,a) for s in sites for a in range(4))
planes=tuple(combinations(range(4),2))
tab=(((1,0),(1,1),(1,2),(1,3)),((1,1),(-1,0),(1,3),(-1,2)),((1,2),(-1,3),(-1,0),(1,1)),((1,3),(1,2),(-1,1),(-1,0)))
def mul(a,b):
  sign,k=tab[a[1]][b[1]]
  return (sign*a[0]*b[0],k)
def inv(a): return a if a[1]==0 else (-a[0],a[1])
def tr(a): return a[0] if a[1]==0 else 0
def shift(s,a):
  z=list(s);z[a]=(z[a]+1)%4;return tuple(z)
def rs(s):return (s[0],s[3],s[1],s[2])
def ra(a):return (0,2,3,1)[a]
def rb(b):return (rs(b[0]),ra(b[1]))
def face(U,s,a,b):
  return tr(mul(mul(mul(U[s,a],U[shift(s,a),b]),inv(U[shift(s,b),a])),inv(U[s,b])))
def action(U):return sum(face(U,s,a,b) for s in sites for a,b in planes)
coarse=[(s,a) for s in sites if all(x%2==0 for x in s) for a in range(4)]
selected={(s,a) for s,a in coarse}|{(shift(s,a),a) for s,a in coarse}
assert len(coarse)==64 and len(selected)==128 and len(set(links)-selected)==896
assert {rb(x) for x in selected}==selected and {rb(x) for x in set(links)-selected}==set(links)-selected
marks=[((0,0,0,0),1,2),((0,0,0,2),1,2)]
rng=Random(20261122)
q8=[(sign,k) for sign in (-1,1) for k in range(4)]
count=0
for _ in range(12):
  U={x:q8[rng.randrange(8)] for x in links}
  V={x:U[rb(x)] for x in links}
  assert action(U)==action(V)
  for s,a in coarse:
    assert mul(V[s,a],V[shift(s,a),a])==mul(U[rs(s),ra(a)],U[shift(rs(s),ra(a)),ra(a)])
    count+=1
  f,g=(face(V,*m) for m in marks)
  assert (f,g)==tuple(face(U,rs(s),ra(a),ra(b)) for s,a,b in marks)
  weight=Q(2)**action(U)
  original=(weight,weight*f,weight*g,weight*f*g)
  assert original==(Q(2)**action(V),Q(2)**action(V)*f,Q(2)**action(V)*g,Q(2)**action(V)*f*g)
  for s,t in product((Q(-9,100),Q(0),Q(9,100)),repeat=2):
    assert sum((a*b for a,b in zip(original,(1,s,t,s*t))),Q(0))==weight*(1+s*f)*(1+t*g)>0
    count+=1
assert count==876
print('PASS 876/876: original 1024-link/1536-plaquette Q8 C3 F19 and four-source tests')
print('Q8 diagnostic only; no continuous SU(N) Haar integration, CMP119/W3 or Agda kernel')
