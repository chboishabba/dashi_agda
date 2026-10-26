#!/usr/bin/env python3
"""Original Griess 1990 grade order13 versus original nonwrapping P3^3 cube.

Reuse source mathematical owners: Robert L. Griess Jr. (1990),
J. Algebra 131:281-293 DOI 10.1016/0021-8693(90)90176-O; DASHI
original Native Cube27+antipode Agda #1249; crystal #1261;
Ibrahim A027907 sequence owner; Lean #52 true Griess rational actor.

Graph voltage/covering framework is external prior art: J. L. Gross
(1974), DOI 10.1016/0012-365X(74)90006-5 and Gross--Tucker
(1977), DOI 10.1016/0012-365X(77)90131-5.
No physical Hamiltonian, selected Monster 3B VOA nor Jordan-product
intertwiner is inferred from grade-set correspondence.
All finite checks exact Python; Lean/Agda kernel verification separate.
"""
from itertools import product,combinations
from collections import Counter,defaultdict,deque
V=list(product(range(3),repeat=3));O=(0,0,0)
neg=lambda x:tuple((-a)%3 for a in x)
canonical=lambda x:min(x,neg(x))
def edge(x,y):
 return sum(a!=b for a,b in zip(x,y))==1 and all(a==b or 0 in (a,b) for a,b in zip(x,y))
def action(x):
 x=list(x)
 for i,j in ((0,1),(1,2),(2,0)):x[i]=(x[i]+x[j])%3
 return tuple(x)
full={frozenset((a,b)) for a,b in combinations(V,2) if edge(a,b)}
punctured=set(V)-{O}
ep={e for e in full if e <= punctured}
axes=sorted({canonical(x) for x in punctured})
eq={frozenset((a,b)) for a,b in combinations(axes,2) if edge(a,b) or edge(a,neg(b))}
assert (len(full),len(ep),len(axes),len(eq))==(54,48,13,24)
assert all(not edge(action(a),action(b)) for a,b in map(tuple,full))
assert all(not edge(action(a),action(b)) for a,b in map(tuple,ep))
projective_image={frozenset((canonical(action(a)),canonical(action(b))))
                  for a,b in map(tuple,eq)}
assert len(projective_image & eq)==5
degrees={a:sum(a in e for e in eq) for a in axes}
assert Counter(degrees.values())=={4:9,3:4}
cycle=[];x=axes[0]
while x not in cycle:
 cycle.append(x);x=canonical(action(x))
assert x==axes[0] and len(cycle)==13 and set(cycle)==set(axes)
assert {degrees[a] for a in cycle}=={3,4}
assert len(eq)%13==11
def connected(vertices,edges):
 adj=defaultdict(set)
 for a,b in map(tuple,edges):adj[a].add(b);adj[b].add(a)
 q=deque([next(iter(vertices))]);seen={q[0]}
 while q:
  for z in adj[q.popleft()]:
   if z not in seen:seen.add(z);q.append(z)
 return seen==set(vertices)
assert connected(punctured,ep) and connected(axes,eq)
assert len(eq)-len(axes)+1==12
assert len(ep)-len(punctured)+1==23
print('PASS original P3^3 cube: 54/54 edges sent to nonedges by genuine source order13 grade word')
print('PASS punctured P3^3: 48/48 edges sent to nonedges')
print('PASS projective 13-axis spatial graph: 24 edges, only 5 preserved; degrees 9x4+4x3')
print('PASS one projective 13-cycle cannot preserve mixed degrees or 24 edges')
print('PASS connected Z2 antipodal cover: cycle ranks 12 -> 23 = 2*12-1')
print('NOT an Albert/Jordan/Monster/physical operator equality')
