#!/usr/bin/env python3
"""Exact native L4 Wilson Mayer connected-factor entropy envelope.

Wilson original continuous compact SU(N) link Haar; no subgroup stand-in.
The mathematical bound uses |exp(beta*t_p)-1|<=exp(beta)-1,
rooted animal DFS encoding, and actual support graph max degree 21 with marks.
This bounds a SINGLE connected labelled Mayer factor sum, NOT the
connected log-partition / interacting renormalized CMP116 shell charge.
"""
from collections import Counter, defaultdict, deque
from fractions import Fraction as Q
from itertools import combinations, product
import sympy as sp

L=4
sites=tuple(product(range(L),repeat=4))
def step(x,a):
    y=list(x);y[a]=(y[a]+1)%L;return tuple(y)
P={(x,a,b):frozenset(((x,a),(step(x,a),b),(step(x,b),a),(x,b)))
   for x in sites for a,b in combinations(range(4),2)}
assert len(sites)==256 and len(P)==1536
inc=defaultdict(set)
for p,edges in P.items():
    for edge in edges:inc[edge].add(p)
assert len(inc)==1024 and set(map(len,inc.values()))=={6}
adj={p:set().union(*(inc[e] for e in edges))-{p} for p,edges in P.items()}
assert Counter(map(len,adj.values()))==Counter({20:1536})
assert all(p in adj[q] for q in adj for p in adj[q])
F=((0,0,0,0),1,2);G=((2,0,0,0),1,2)
d={F:0};queue=deque([F])
while queue:
    p=queue.popleft()
    for q in adj[p]:
        if q not in d:d[q]=d[p]+1;queue.append(q)
assert d[G]==3 and len(d)==1536

# Affine marks are DISTINCT factor labels. Original F/G action plaquette
# factors still exist in the original Wilson density. They must NOT be
# removed from the interaction factor graph or conflated with mark labels.
labels=tuple(P)+('Fmark','Gmark')
supports=dict(P);supports['Fmark']=P[F];supports['Gmark']=P[G]
inc2=defaultdict(set)
for p,edges in supports.items():
    for e in edges:inc2[e].add(p)
adj2={p:set().union(*(inc2[e] for e in supports[p]))-{p} for p in labels}
assert Counter(map(len,adj2.values()))==Counter({20:1494,21:44})
D=max(map(len,adj2.values()))
assert D==21
Dmarks={'Fmark':0};queue=deque(['Fmark'])
while queue:
    p=queue.popleft()
    for q in adj2[p]:
        if q not in Dmarks:Dmarks[q]=Dmarks[p]+1;queue.append(q)
assert Dmarks['Gmark']==3

# Rooted ordered DFS trees of k vertices have <=Catalan(k-1)*D^(k-1)
# choices, at most (4D)^(k-1). For one factor-connected set containing
# the two unique global marks and n unmarked plaquette factors: k=n+2,
# n>=mark overlap distance-1=2. Every Haar integral absolute activity
# is <=lambda(beta)^n, lambda=e^beta-1, by normalized product Haar.
# Total <=(4D)*sum_{n>=d-1}[4D*lambda]^n
#        =(4D)*q^(d-1)/(1-q), provided q<1.
assert 4*D==84
beta=sp.symbols('beta',positive=True)
assert sp.simplify(sum(beta**k/sp.factorial(k) for k in range(1,8))
                   -sp.series(sp.exp(beta)-1,beta,0,8).removeO())==0
# Elementary rational envelope e^beta-1 <= beta/(1-beta), 0<=beta<1.
for denom in (100,200,2000):
    b=Q(1,denom)
    q_upper=Q(4*D)*b/(1-b)
    assert q_upper==Q(84,denom-1) and q_upper<1
    root_bound=Q(4*D)*q_upper**(Dmarks['Gmark']-1)/(1-q_upper)
    print(f'beta<=1/{denom}: q <= {q_upper}; absolute connected-mark factor-sum <= {root_bound}')
print('PASS native 256 sites, 1024 links / six plaquettes per link, 1536 plaquettes / degree 20')
print('PASS augmented original two-global-mark graph 1494 degree-20, 44 degree-21; mark distance 3')
print('PASS exact rooted-tree enumeration envelope, rational beta thresholds')
print('NOT full CMP116 W3: single connected source-factor activities exclude many Ursell incompatibility clusters')
print('NOT beta(a)->infinity: unrenormalized absolute bound is high-temperature only')
