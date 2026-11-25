from itertools import product, combinations, permutations
from collections import Counter
import sympy as s

def require(ok):
    if not ok: raise AssertionError('projective pencil / cone check failed')
T=(-1,0,1)
def bal(x): return (x+1)%3-1
def vec(v): return tuple(map(bal,v))
def neg(v): return tuple(-x for x in v)
def canon(v):
    v=vec(v); return neg(v) if next(x for x in v if x)!=1 else v
def dot(a,b): return sum(x*y for x,y in zip(a,b))%3
P=sorted({canon(v) for v in product(T,repeat=3) if any(v)})
L=[{p for p in P if dot(p,n)==0} for n in P]
pole=(0,0,1)
B=sorted({canon(v) for v in product(T,repeat=2) if any(v)})
fibres=[{(a,b,k) for k in T} for a,b in B]
require(len(P)==13 and len(L)==13 and all(len(l)==4 for l in L))
require(set.union(*fibres)==set(P)-{pole} and sum(map(len,fibres))==12)
require({frozenset(f|{pole}) for f in fibres}=={frozenset(l) for l in L if pole in l})
for p,q in combinations(P,2): require(sum(p in l and q in l for l in L)==1)
# Signed source reconstructed without identifying the pole with the origin.
for v in product(T,repeat=3):
    if any(v):
        p=canon(v); sign=next(x for x in v if x)
        require(tuple(sign*x for x in p)==v)
# Cube triple incidence and complete quadrangle.
corners=list(product((-1,1),repeat=3))
E=Counter()
for c in corners:
    x,y,z=c; edges=((x,y,0),(x,0,z),(0,y,z)); E.update(edges)
    require(tuple(sum(e[j] for e in edges)//2 for j in range(3))==c)
require(len(E)==12 and set(E.values())=={2})
V=[v for v in corners if v[0]*v[1]*v[2]==1]
Sums=set(); Diffs=set()
for u,w in combinations(V,2):
    a=canon(tuple(x+y for x,y in zip(u,w))); b=canon(tuple(x-y for x,y in zip(u,w)))
    Sums.add(a); Diffs.add(b)
    require({canon(u),canon(w),a,b} in L)
require(len(Sums)==3 and len(Diffs)==6 and len({canon(v) for v in V})==4)
require(Sums|Diffs|{canon(v) for v in V}==set(P))
# Every pencil-preserving projective map has a unique block representative
# [[A,0],[l,1]]. Enumerate all 432; none has order 4 on P with a 4-cycle on B.
def mv(A,v): return vec(sum(a*b for a,b in zip(row,v)) for row in A)
def cycles(perm):
    unseen=set(perm); lens=[]
    while unseen:
        u=next(iter(unseen)); v=u; n=0
        while v in unseen: unseen.remove(v); n+=1; v=perm[v]
        require(v==u); lens.append(n)
    return sorted(lens)
actors=base4=0
for a,b,c,d in product(T,repeat=4):
    if (a*d-b*c)%3==0: continue
    A=((a,b),(c,d)); base={p:canon(mv(A,p)) for p in B}
    for l,m in product(T,repeat=2):
        M=((a,b,0),(c,d,0),(l,m,1)); perm={p:canon(mv(M,p)) for p in P}
        actors+=1
        require({frozenset(perm[p] for p in line) for line in L}=={frozenset(line) for line in L})
        if cycles(base)==[4]:
            base4+=1; require(cycles(perm)==[1,4,8])
require(actors==432 and base4==108)
# The actual C4 x C3 action on labelled pencil fibres is a bijection,
# not a collineation. Retain chart vs incidence distinction.
chart={(j,k):(a,b,k) for j,(a,b) in enumerate(B) for k in T}
for h,k in product(range(4),T):
    perm={pole:pole,**{p:chart[((j+h)%4,bal(t+k))] for (j,t),p in chart.items()}}
    require(len(set(perm.values()))==13)
    if h==1 and k==0: require({frozenset(perm[p] for p in l) for l in L}!={frozenset(l) for l in L})
# Tetrahedral null frame: null requirement selects collective weight.
M=s.Matrix(V).T; one=s.ones(4,1); lam=s.symbols('lambda',real=True)
require(M*M.T==4*s.eye(3) and M*one==s.zeros(3,1))
G=M.T*M-lam*one*one.T
require(G==4*s.eye(4)-(1+lam)*one*one.T)
require(G.subs(lam,3).eigenvals()=={-12:1,4:3})
require(G.subs(lam,3).diagonal()==s.zeros(1,4))
require(G.subs(lam,-1)==4*s.eye(4))
# Negacyclic signed shift: x^12+1, C3 restriction, distinct pointed completion.
R=s.zeros(12)
for j in range(11): R[j+1,j]=1
R[0,11]=-1
x=s.symbols('x'); require(R**12==-s.eye(12) and R**24==s.eye(12))
require(R.charpoly(x).as_expr()==x**12+1)
require(s.factor((R**8).charpoly(x).as_expr())==(x-1)**4*(x*x+x+1)**4)
# Signed cycle section: 4 triples with holonomy +1, gauge transport to positive cycles.
for j in range(4):
    e=s.eye(12)[:,j]; require((R**8)**3*e==e)
    require(len({tuple((R**8)**k*e) for k in range(3)})==3)
require(s.expand((x**4+1)*(x**8-x**4+1))==x**12+1)
# A pointed trivial summand changes characteristic polynomial, not the +1 term.
require(s.diag(R,1).charpoly(x).as_expr()==s.expand((x-1)*(x**12+1)))
print(f'PASS 27 signed points, 13 projective points, 78 point pairs, 24 corner-edge incidences, {actors} collineations, {base4} base-four-cycle lifts, 12 labelled phase actions, tetrahedral null Gram, signed negacyclic spectrum')
