#!/usr/bin/env python3
"""Original Griess F3^3 source grade action versus original P3^3-0 graph.
Original owners: R. L. Griess Jr. (1990), J Algebra 131:281-293;
Agda #1249 native graph, #1261 projective axes, Lean #52 Griess grades.
Group averaging is classical Reynolds invariant theory; graph-cover
language Gross 1974 / Gross–Tucker 1977. No kernel/physical/VOA proof.
Standard-library-only exact rational acceptance test.
"""
from itertools import product,combinations
from collections import Counter,deque
from fractions import Fraction as Q
V=tuple(v for v in product(range(3),repeat=3) if v!=(0,0,0))
def signed(v):return tuple(x if x!=2 else -1 for x in v)
def shear(v,i,j):
 w=list(v);w[i]=(w[i]+w[j])%3;return tuple(w)
def word(v):
 for i,j in ((0,1),(1,2),(2,0)):v=shear(v,i,j)
 return v
idx={v:i for i,v in enumerate(V)}
N=26;pi=tuple(idx[word(v)] for v in V)
powers=[tuple(range(N))]
for _ in range(12):powers.append(tuple(pi[i] for i in powers[-1]))
assert tuple(pi[i] for i in powers[-1])==powers[0]
def adj(x,y):return int(sum(abs(a-b) for a,b in zip(signed(x),signed(y)))==1)
A=tuple(tuple(adj(x,y) for y in V) for x in V)
Z=tuple(tuple(sum(A[p[i]][p[j]] for p in powers) for j in range(N)) for i in range(N))
sq=lambda B:sum(v*v for row in B for v in row)
inner=lambda B,C:sum(B[i][j]*C[i][j] for i in range(N) for j in range(N))
assert sq(A)==96 and sq(Z)==3120 and inner(A,Z)==240
assert all(Z[i][j]==Z[pi[i]][pi[j]] for i in range(N) for j in range(N))
assert sum((13*A[i][j]-Z[i][j])**2 for i in range(N) for j in range(N))==13104
pairs=set(combinations(range(N),2));hist=Counter()
while pairs:
 i,j=min(pairs);orbit=set()
 for _ in range(13):
  orbit.add(tuple(sorted((i,j))));i,j=pi[i],pi[j]
 assert len(orbit)==13
 pairs-=orbit
 hist[sum(A[i][j] for i,j in orbit)]+=1
assert hist=={0:3,1:6,2:6,3:10}
neg=lambda v:tuple((-x)%3 for x in v)
R=tuple(sorted({min(v,neg(v)) for v in V}))
ev=tuple(tuple(Z[idx[a]][idx[b]]+Z[idx[a]][idx[neg(b)]] for b in R) for a in R)
od=tuple(tuple(Z[idx[a]][idx[b]]-Z[idx[a]][idx[neg(b)]] for b in R) for a in R)
assert (sq(ev),sq(od))==(2912,208)
assert (Q(sq(Z),169*96),Q(13104,169*96))==(Q(5,26),Q(21,26))
assert (Q(sq(ev),169*48),Q(sq(od),169*48))==(Q(14,39),Q(1,39))
# Complete full SL(3,3) pair orbits under its ORIGINAL SIX grade shears.
todo_pairs=set(product(V,repeat=2));orbits=[]
generators=[(i,j) for i in range(3) for j in range(3) if i!=j]
while todo_pairs:
 start=min(todo_pairs);todo=deque([start]);orbit={start}
 while todo:
  x,y=todo.popleft()
  for i,j in generators:
   n=(shear(x,i,j),shear(y,i,j))
   if n not in orbit:orbit.add(n);todo.append(n)
 todo_pairs-=orbit;orbits.append(orbit)
assert sorted(map(len,orbits))==[26,26,624]
kind=lambda x,y:'equal' if x==y else 'opposite' if x==neg(y) else 'independent'
summary={kind(*min(o)):(len(o),sum(A[idx[x]][idx[y]] for x,y in o)) for o in orbits}
assert summary=={'equal':(26,0),'opposite':(26,0),'independent':(624,96)}
W=tuple(tuple(Q(0) if x==y or x==neg(y) else Q(2,13) for y in V) for x in V)
assert sq(W)==Q(192,13)
assert sq(tuple(tuple(A[i][j]-W[i][j] for j in range(N)) for i in range(N)))==Q(1056,13)
fullodd=tuple(tuple(W[idx[a]][idx[b]]-W[idx[a]][idx[neg(b)]] for b in R) for a in R)
assert all(all(x==0 for x in row) for row in fullodd)
print('PASS original C13 Reynolds: 25 pair orbits',sorted(hist.items()))
print('PASS C13 Frobenius loss 21/26, retained 5/26; signed13 retained 1/39')
print('PASS original full SL3(3): 26+26+624 ordered-grade pair orbits')
print('PASS full SL3 projection (2/13)*(J-I-antipode), retain 2/13, loss 11/13')
print('PASS full SL3 projection annihilates entire odd signed spatial 13D block')
print('NOT an original physical/Jordan/Monster same-object action or Lean/Agda kernel receipt')
