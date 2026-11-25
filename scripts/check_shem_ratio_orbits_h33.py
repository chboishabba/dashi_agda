from sympy import Poly, symbols, __version__
from itertools import product, permutations
from collections import Counter
from math import log2
x=symbols('x'); p=Poly(x**3-x-1,x,modulus=3); assert p.is_irreducible
V=list(range(27)); ds=lambda a:[a%3,a//3%3,a//9]
num=lambda a:sum((v%3)*3**i for i,v in enumerate(a))
A=[[num([u+v for u,v in zip(ds(a),ds(b))]) for b in V] for a in V]
D=[[num([u-v for u,v in zip(ds(a),ds(b))]) for b in V] for a in V]
P=[Poly(sum(v*x**i for i,v in enumerate(ds(a))),x,modulus=3) for a in V]
M=[[num([int(q.nth(i)) for i in range(3)]) for b in V for q in [(P[a]*P[b]).rem(p)]] for a in V]
I=[0]+[M[a].index(1) for a in V[1:]]
def ratio(a,b,c):return M[D[c][a]][I[D[b][a]]]
left=set(V)-{0,1}; orbits=[]
while left:
 r=min(left); o={ratio(*t) for t in permutations((0,1,r))}; orbits.append(sorted(o)); left-=o
assert [len(o) for o in orbits]==[1,6,6,6,6]
lookup={r:i for i,o in enumerate(orbits) for r in o}
def code(a,b,c):
 if a==b:return 'allEqual' if a==c else 'equalAnchors'
 if c==a:return 'equalsFirst'
 if c==b:return 'equalsSecond'
 return lookup[ratio(a,b,c)]
for a,b in product(V,repeat=2):
 hist=Counter(code(a,b,c) for c in V)
 assert hist==({'allEqual':1,'equalAnchors':26} if a==b else {'equalsFirst':1,'equalsSecond':1,**{i:len(o) for i,o in enumerate(orbits)}})
checks=0
for a,b,c in product(V,repeat=3):
 if len({a,b,c})==3:
  assert all(code(*t)==code(a,b,c) for t in permutations((a,b,c)));checks+=6
print(__version__,orbits,'pair partitions',729,'permutation checks',checks)
print('oracle sheet remaining counts / bits by role',[(6**54*26**k,54*log2(6)+k*log2(26)) for k in (6,5,5)])
