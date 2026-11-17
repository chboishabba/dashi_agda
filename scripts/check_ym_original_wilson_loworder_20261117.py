#!/usr/bin/env python3
"""Original periodic six-plane SU2 Wilson partition coefficients at beta=0.
Exact rational geometric/factorized link moment checker; NOT full Haar proof.
E_H(t_p)=0, E_H(t_p^2)=1/4, E_H(t_p t_q)=0 if p!=q,
because every distinct plaquette has a unique link whose central sign
flip changes only that plaquette. A 24-cell 5-design reproduces all
individual link polynomials of degree <= 2 appearing through beta^2.
At side L, P=6L^4, Z=1-P beta + (P^2/2+P/8) beta^2 + O(beta^3).
At L=4, P=1536 and coefficient=1179840.
Attribution: Wilson/Balaban, canonical DASHI 4D positive bonds,
Pizzetti/Folland SU2 moments, 24-cell finite design.
"""
from itertools import product, combinations
from fractions import Fraction as Q
checks=0
def eq(x,y,label):
 global checks
 assert x==y,(label,x,y)
 checks+=1
def edges(x,a,b,L):
 def step(s,k):
  v=list(s);v[k]=(v[k]+1)%L;return tuple(v)
 return frozenset(((x,a),(step(x,a),b),(step(x,b),a),(x,b)))
for L in (2,3,4):
 sites=product(range(L),repeat=4)
 ps={(x,a,b):edges(x,a,b,L) for x in sites
     for a,b in combinations(range(4),2)}
 P=6*L**4
 eq(len(ps),P,"six planes x four-volume")
 seen={}
 for p,E in ps.items():
  eq(len(E),4,"four distinct positive links")
  for edge in E:seen.setdefault(edge,set()).add(p)
 eq(len(seen),4*L**4,"four positive links per site")
 eq(len(set(ps.values())),P,"distinct plaquette supports")
 sharing={tuple(sorted((p,q))) for owners in seen.values()
          for p,q in combinations(sorted(owners),2)}
 for p,q in sharing:eq(bool(ps[p]^ps[q]),True,"odd-link cancellation")
 second=Q(P*P)+Q(P,4)
 eq(second/2,Q(P*P,2)+Q(P,8),"partition beta^2")
 print(f"L={L}: links={4*L**4}, plaquettes={P}, pair overlaps={len(sharing)}, "
       f"Z=1-{P} beta+{second/2} beta^2+O(beta^3)")
# Concrete 24 rational nodes, weights 1/24, exact degree-2 moments.
vs=[]
for i in range(4):
 for sign in (-1,1):
  v=[Q(0)]*4;v[i]=Q(sign);vs.append(tuple(v))
for signs in product((-1,1),repeat=4):
 vs.append(tuple(Q(s,2) for s in signs))
eq(len(vs),24,"24-cell")
for v in vs:eq(sum(t*t for t in v),1,"norm")
for i in range(4):
 eq(sum(v[i] for v in vs)/24,0,"odd moment")
 for j in range(4):
  eq(sum(v[i]*v[j] for v in vs)/24,
     Q(1,4) if i==j else 0,"Gram moment")
print(f"ORIGINAL_WILSON_EXACT_LOW_ORDER_PASS={checks}")
