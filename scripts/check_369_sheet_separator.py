from itertools import product
from collections import Counter
import sympy as s
T=(-1,0,1)
R=s.Matrix([[0,-1,0],[1,0,0],[0,0,1]])
assert R.det()==1 and R.T*R==s.eye(3)
def turn(x):return (-x[1],x[0],x[2])
def back(x):return (x[1],-x[0],x[2])
assert all(back(turn(x))==x and turn(back(x))==x for x in product(T,repeat=3))
# Checkerboard elimination: interiors independent, boundary retained.
for d in (2,3):
 P=list(product(range(3),repeat=d)); E=[(p,q) for p in P for q in P if p<q and sum(abs(a-b) for a,b in zip(p,q))==1]
 I=[p for p in P if sum(p)%2==1]; B=[p for p in P if p not in I]
 assert all(not (p in I and q in I) for p,q in E)
 N={p:sorted(q if p==r else r for r,q in E if p in (r,q)) for p in I}
 # Signed weights deterministic and reproducible.
 W={e:(i%5)-2 for i,e in enumerate(E)}
 def w(p,q):return W[tuple(sorted((p,q)))]
 for alphabet in ((0,1),T):
  tables={}; checks=0
  for p,ns in N.items():
   table={}
   for a in product(alphabet,repeat=len(ns)):
    v,x=max((sum(w(p,q)*(x!=y) for q,y in zip(ns,a)),x) for x in alphabet)
    assert v==sum(w(p,q)*(x!=y) for q,y in zip(ns,a))
    assert all(v>=sum(w(p,q)*(z!=y) for q,y in zip(ns,a)) for z in alphabet)
    table[a]=(v,x);checks+=1
   tables[p]=table
  # Exhaustive sheet boundary; sampled cube boundary, independent factorwise check.
  assignments=product(alphabet,repeat=len(B)) if d==2 else (tuple(alphabet[(i+j*j)%len(alphabet)] for j in range(len(B))) for i in range(20))
  count=0
  for a in assignments:
   b=dict(zip(B,a)); v=0
   for p,ns in N.items():
    val,x=tables[p][tuple(b[q] for q in ns)];v+=val;b[p]=x
   assert sum(w(p,q)*(b[p]!=b[q]) for p,q in E)==v
   count+=1
  print(d,len(alphabet),'sites',len(P),'edges',len(E),'removed',len(I),'degree',dict(Counter(map(len,N.values()))),'table entries',checks,'reconstructed',count,'raw edge entries',len(E)*len(alphabet)**2)
print('SymPy',s.__version__,'PASS')
