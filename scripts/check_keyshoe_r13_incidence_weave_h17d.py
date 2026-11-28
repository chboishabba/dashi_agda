"""H17d exact candidate geometry: H17 signed R13, H3 line/conic, H8 source masks.
Independent source and value cubes; no source cipher recognition or Agda claim.
"""
from itertools import product, combinations
from collections import Counter
import json
import sympy as sp
from check_keyshoe_r13_trigram_h17 import slots, L, G, act, orbit, field
Z=(0,0,0); V=[Z]+[field(x) for x in L]; X=tuple(slots[l] for l in 'NPW'); O=orbit(X)
assert len(set(V))==27
F={x:field(x) for x in L}; Fi={v:x for x,v in F.items()}
def neg(v):return tuple((-a)%3 for a in v)
def proj(v):return tuple((a*next(b for b in v if b))%3 for a in v)
def inv(v):
 if v==Z:return Z
 j,s=Fi[v];return F[(-j%13,s)]
assert all(inv(inv(v))==v and inv(neg(v))==neg(inv(v)) for v in V)
axes=sorted({proj(v) for v in V if v!=Z})
def dot(a,b):return sum(x*y for x,y in zip(a,b))%3
lines=[frozenset(v for v in axes if dot(n,v)==0) for n in axes]
conics=[frozenset(proj(inv(v)) for v in l) for l in lines]
assert len(set(lines))==len(set(conics))==13 and not set(lines)&set(conics)
assert all(Counter(len(c&l) for l in lines)=={0:3,1:4,2:6} for c in conics)
t=sp.symbols('t'); p=sp.Poly(t**3-t-1,t,modulus=3)
assert p.is_irreducible
def P(v):return sp.Poly(sum(a*t**i for i,a in enumerate(v)),t,modulus=3)
def power(v,n):return tuple(int((P(v)**n).rem(p).nth(i))%3 for i in range(3))
Q={v:tuple(int((P(power(v,3))*P(power(v,9))).rem(p).nth(i))%3 for i in range(3)) for v in V}
e=[(1,0,0),(0,1,0),(0,0,1)]
for n,c in zip(axes,conics):
 assert c=={v for v in axes if dot(n,Q[v])==0}
 q=lambda v:dot(n,Q[v]); M=sp.Matrix(3,3,lambda i,j:2*(q(tuple((a+b)%3 for a,b in zip(e[i],e[j])))-q(e[i])-q(e[j]))%3)
 assert M.det()%3!=0
# Index bits: inversion, global sign, role reversal. NOT the H8 source mask.
def val(mask,v):
 if mask&1:v=inv(v)
 if mask&2:v=neg(v)
 return v
def trip(mask,x):
 y=tuple(val(mask,v) for v in x)
 return y[::-1] if mask&4 else y
base={tuple(F[x] for x in y) for y in O}
assert not base&{v[::-1] for v in base}
R={m:{trip(m,x) for x in base} for m in range(8)}
A={m:conics if m&1 else lines for m in range(8)}
counts=Counter()
for m in range(8):
 for n in range(8):
  for x in R[m]:
   y=trip(m^n,x);assert y in R[n] and trip(m^n,y)==x
   assert trip(n,y)==trip(m,x);counts['triplet_inverse']+=1
  for i,l in enumerate(A[m]):
   for v in axes:
    w=proj(val(m^n,v));assert (v in l)==(w in A[n][i]);counts['incidence']+=1
  for k in range(8):
   for x in R[m]:
    assert trip(n^k,trip(m^n,x))==trip(m^k,x);counts['triplet_composition']+=1
 for missing in range(3):
  d={}
  for x in R[m]:
   pair=tuple(v for i,v in enumerate(x) if i!=missing)
   assert pair not in d;d[pair]=x[missing]
  assert len(d)==52
  for a,b in product(V,repeat=2):
   matches=[x[missing] for x in R[m] if tuple(v for i,v in enumerate(x) if i!=missing)==(a,b)]
   assert matches==([d[a,b]] if (a,b) in d else []);counts['pair_query']+=1
for i,j in combinations((1,2,4),2):
 for m in (0,7^(i|j)):
  for x in R[m]:
   assert trip(j,trip(i,x))==trip(i,trip(j,x));counts['letter_face']+=1
C=list(product(range(3),range(8),range(-1,2),range(-1,2)))
def source(mask,x):
 r,q,a,b=x
 if mask&1 and r==1:r,q,a,b=r,7-q,-a,-b
 if mask&2:r,q,a,b=2-r,7-q,-a,-b
 if mask&4:q^=4
 return r,q,a,b
cols=[tuple((r,q,a,b) for r in range(3)) for q,a,b in product(range(8),range(-1,2),range(-1,2))]
for m in range(8):
 cs=[tuple(source(m,x) for x in col) for col in cols]
 assert set(x for col in cs for x in col)==set(C)
 assert all(source(m,y)==x for col,ys in zip(cols,cs) for x,y in zip(col,ys))
 for n,k in product(range(8),repeat=2):
  for x in C:
   assert source(n^k,source(m^n,source(m,x)))==source(m^k,source(m,x));counts['source_composition']+=1
aligned={m:sum(len({x[1:] for x in col})==1 for col in (tuple(source(m,x) for x in col) for col in cols)) for m in range(8)}
assert aligned=={m:0 if m&1 else 72 for m in range(8)}
for m,n in product(range(8),repeat=2):
 for x,y in product(C,base):
  assert (source(m,source(m,x)),trip(n,trip(n,y)))==(x,y);counts['product_inverse']+=1
assert sum(neg(v)==v for v in V)==1
assert sum(inv(v)==v for v in V)==3
print(json.dumps({'counts':dict(counts),'aligned_source_columns':aligned,'letter_orbit_sizes':{m:len(R[m]) for m in R},'line_conic_intersections':dict(Counter(len(c&l) for l in lines for c in conics)),'hebrew_fixed_count':17,'sign_fixed_count':1,'inversion_fixed_count':3},sort_keys=True))
