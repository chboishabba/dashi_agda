#!/usr/bin/env python3
"""Particle-suite BIDI finite audit: original E32/E21 weights, Wilson index,
crystal signed axes, and zero-mode consumer square.
Classical: E6 branching, Fourier averaging, SM anomalies. Original DASHI
#1106/#1241 E6 weight and Higgs owners, punctured27/PG13 crystal owner,
ZetaIrrationalFibreCommutingSquareBidiExact and three-harmonic Weyl owner.
New: arithmetic join; no physical masses, chirality selection or QFT claim.
"""
from collections import Counter
from itertools import product
from fractions import Fraction as F
import sympy as s
l=(1,1,-2); r=(4,-2,-2); le=(-2,4,-2)
rows=[]
for i,j in product(range(3),repeat=2):
    rows.extend([('A',1,int(j<2),l[j],le[j]//2),('B',2,0,-r[j],-r[j]//2),('C',0,int(i<2),r[j]-l[i],(r[j]-le[i])//2)])
assert len(rows)==27
assert all((t+q)%3==0 for b,t,w,y,q in rows)
weights=Counter((t,w,y) for b,t,w,y,q in rows)
sm=Counter({(1,1,1):6,(2,0,-4):3,(2,0,2):3,(0,1,-3):2,(0,0,6):1,(0,0,0):1})
extra=Counter({(1,0,-2):3,(2,0,2):3,(0,1,3):2,(0,1,-3):2,(0,0,0):1})
assert weights==sm+extra
counts={'A':(7,4),'B':(7,4),'C':(9,6)}
positive=Counter(); conjugate=Counter()
for b,t,w,y,q in rows:
    positive[t,w,y]+=counts[b][0]
    conjugate[(3-t)%3,w,-y]+=counts[b][1]
assert sum(positive.values())==207 and sum(conjugate.values())==126
net=Counter()
for b,t,w,y,q in rows:net[t,w,y]+=counts[b][0]-counts[b][1]
assert net==Counter({k:3*v for k,v in weights.items()})
for c in (positive+conjugate,sm,extra):
    assert sum(m*y for (t,w,y),m in c.items())==0
    assert sum(m*y**3 for (t,w,y),m in c.items())==0
    assert sum(m//3*y for (t,w,y),m in c.items() if t)==0
    assert sum(m//2*y for (t,w,y),m in c.items() if w)==0
    assert sum(m*(1 if t==1 else -1) for (t,w,y),m in c.items() if t)==0
    assert sum(m//2 for (t,w,y),m in c.items() if w)%2==0
T=(-1,0,1); cube=set(product(T,repeat=3)); holes={(-1,0,1),(0,1,-1),(1,-1,0)}
neg=lambda p:tuple(-a for a in p)
W=cube-holes-{(0,0,0)}
axes={min(p,neg(p)) for p in W}
assert len(axes)==13
assert sum(p in W and neg(p) in W for p in axes)==10
assert len(W)==23
assert Counter(sum(a!=0 for a in p) for p in W)=={1:6,2:9,3:8}
C=s.Matrix([[0,0,1],[1,0,0],[0,1,0]])
E=(s.eye(3)+C+C**2)/3
v=s.Matrix([1,-1,0]); w=v
assert E*v==s.zeros(3,1)
assert E*s.matrix_multiply_elementwise(v,w)==s.ones(3,1)*F(2,3)
assert any(t%3!=(-t)%3 for _,t,_,_,_ in rows)
assert 78==24+27+27 and 24==8+8+8 and 12==8+3+1
print('PASS 27 source charge weights; full 207+126 Weyl internal labels; net 81')
print('PASS 3*(16+10+1), full and per-sector anomaly sums')
print('PASS 23 crystal sites = 10 signed pairs + 3 singles; strata 6+9+8')
print('PASS zero-mode product counterexample and charge-preserving inversion obstruction')
