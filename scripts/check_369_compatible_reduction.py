from itertools import product
from time import perf_counter
import sympy as s
# Selected consumer: sum of local signed nearest-neighbour disagreement costs.
# Disjoint interiors on a path, including arbitrary signed edge weights.
def score(a,b,w): return w*int(a!=b)
def eliminate(w,v):
 return {(a,b):max((score(a,x,w)+score(x,b,v),x) for x in (-1,0,1)) for a,b in product((-1,0,1),repeat=2)}
# Exact boundary table and deterministic witness for every boundary assignment.
checks=0
for w,v in product(range(-2,3),repeat=2):
 t=eliminate(w,v)
 for (a,b),(value,x) in t.items():
  assert value==score(a,x,w)+score(x,b,v)
  assert all(value>=score(a,y,w)+score(y,b,v) for y in (-1,0,1))
  checks+=1
# Binary MAX-CUT path: max-plus transfer matrices with reconstruction.
def reduce_path(weights):
 levels=[]; tables=[[[0,w],[w,0]] for w in weights]; counts=[len(tables)]
 while len(tables)>1:
  nxt=[]; rec=[]
  for k in range(0,len(tables)-1,2):
   A,B=tables[k:k+2]; pairs=[[max((A[a][x]+B[x][b],x) for x in range(2)) for b in range(2)] for a in range(2)]
   nxt.append([[p[0] for p in row] for row in pairs]); rec.append([[p[1] for p in row] for row in pairs])
  odd=len(tables)%2
  if odd:nxt.append(tables[-1])
  levels.append((rec,odd)); tables=nxt;counts.append(len(tables))
 value,a,b=max((tables[0][a][b],a,b) for a,b in product(range(2),repeat=2)); bits=[a,b]
 for rec,odd in reversed(levels):
  out=[bits[0]]
  for k,r in enumerate(rec):out.extend((r[bits[k]][bits[k+1]],bits[k+1]))
  if odd:out.append(bits[-1])
  bits=out
 assert sum(w*(a!=b) for w,a,b in zip(weights,bits,bits[1:]))==value
 return value,counts
for n in range(1,8):
 for w in product((-1,0,2),repeat=n):
  assert reduce_path(w)[0]==sum(max(0,x) for x in w)
print('SymPy',s.__version__,'ternary boundary certificates',checks,'binary paths',sum(3**n for n in range(1,8)))
for n in (1024,4096,16384):
 w=[(i%7)-3 for i in range(n)]; t=perf_counter(); val,c=reduce_path(w); print(n,c,'score',val,'seconds',round(perf_counter()-t,5))
