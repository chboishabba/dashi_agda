from itertools import product
from collections import Counter
import sympy as s
T=(-1,0,1)
P=list(product(T,repeat=3))
def support(p): return tuple(abs(x) for x in p)
def signs(p): return tuple(x for x in p if x)
def reopen(m,r):
 it=iter(r); return tuple(next(it) if b else 0 for b in m)
def edge(p,q): return sum(abs(a-b) for a,b in zip(p,q))==1
def neg(p): return tuple(-x for x in p)
def rot(p): return p[1:]+p[:1]
assert all(reopen(support(p),signs(p))==p for p in P)
E={(p,q) for p in P for q in P if edge(p,q)}
assert len(E)==108
assert all((neg(p),neg(q)) in E and (rot(p),rot(q)) in E for p,q in E)
p=(-1,0,0); q=(0,0,0); r=(1,0,0)
assert support(p)==support(r) and edge(p,q) and edge(q,r) and not edge(p,r)
a=(-1,0,0); b=(-1,1,0); c=(1,1,0)
assert support(b)==support(c) and edge(a,b) and not edge(a,c)
B=list(product((0,1),repeat=3)); BE={(m,n) for m in B for n in B if edge(m,n)}
assert {(support(p),support(q)) for p,q in E}==BE and len(BE)==24
counts=Counter((support(p),support(q)) for p,q in E)
assert all(counts[m,n]==2**max(sum(m),sum(n)) for m,n in BE)
for m in B:
 rows=[Counter(support(q) for q in P if edge(p,q)) for p in P if support(p)==m]
 assert all(row==rows[0] for row in rows)
A=s.Matrix([[int(edge(p,q)) for q in P] for p in P]); H=s.Matrix([[int(support(p)==m) for m in B] for p in P]); Q=s.Matrix([[0]*8 for _ in B])
for i,m in enumerate(B):
 for j,n in enumerate(B):
  if (m,n) in BE: Q[i,j]=2 if sum(n)>sum(m) else 1
assert A*H==H*Q
Z=(-1,'-0','+0',1); coarse={-1:-1,'-0':0,'+0':0,1:1}
assert coarse[Z[1]]==coarse[Z[2]] and Z[1]!=Z[2]
print('SymPy',s.__version__,'27 codec roundtrips; 108 signed arcs; 24 support arcs; equivariance and collision PASS; equitable quotient A H = H Q PASS')
