from itertools import product, permutations
from functools import lru_cache
T=(-1,0,1)
P=tuple(permutations(T))
def act(p,b): return tuple(p[T.index(x)] for x in b)
@lru_cache(None)
def canon(b): return min((act(p,b),p) for p in P)
def score(w,b,a): return sum(v*(a!=x) for v,x in zip(w,b))
def solve(w,b): return max((score(w,b,a),a) for a in T)
checks=0
for k in range(1,7):
 B=list(product(T,repeat=k)); reps={canon(b)[0] for b in B}
 assert len(reps)==(3**k+3)//6
 for w in [tuple((i+j)%5-2 for i in range(k)) for j in range(5)]:
  table={r:solve(w,r) for r in reps}
  for b in B:
   r,p=canon(b); v,a=table[r]; original=T[p.index(a)]
   assert score(w,b,original)==v==solve(w,b)[0]
   checks+=1
 print(k,len(B),len(reps))
# A zero-sensitive unary breaks full label symmetry, not antipodal symmetry.
unary=lambda a: int(a==0)
assert all(unary(a)==unary(-a) for a in T)
assert any(unary(a)!=unary(act(p,(a,))[0]) for a in T for p in P)
print('witness checks',checks)
