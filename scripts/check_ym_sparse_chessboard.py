"""Exact geometry and algebra for the site-reflection chessboard bound.
Not a numerical integration or Agda kernel check."""
import sympy as s
from itertools import product, combinations
from collections import Counter

for L in (4,8,12):
    P = [(x,i,j) for x in product(range(L),repeat=4) for i,j in combinations(range(4),2)]
    # Unit cubes: transverse reflected corner lies on the even plane.
    # Four shifts cover all transverse parity classes.
    for i,j in combinations(range(4),2):
        transverse=[k for k in range(4) if k not in (i,j)]
        for shift in product(range(2),repeat=2):
            marks=[]
            for tile in product(range(L),repeat=4):
                x=list(tile)
                for k,h in zip(transverse,shift):
                    x[k]=(tile[k]+tile[k]%2+h)%L
                marks.append(tuple(x))
            counts=Counter(marks)
            assert len(counts)==L**4//4 and set(counts.values())=={4}
            assert set(counts)=={x for x in product(range(L),repeat=4) if all(x[k]%2==h for k,h in zip(transverse,shift))}
            assert len({tuple((x[k]-dict(zip(transverse,shift)).get(k,0))%L for k in range(4)) for x in counts})==len(counts)
    inc=Counter()
    for x,i,j in P:
        def shift(k): return tuple((a+(t==k))%L for t,a in enumerate(x))
        for e in ((x,i),(x,j),(shift(i),j),(shift(j),i)): inc[e]+=1
    assert set(inc.values())=={6} and len(inc)==4*L**4
beta, eps, C = s.symbols('beta eps C', positive=True)
assert s.expand((-beta*eps/4+6*C)/24-(-beta*eps/96+C/4))==0
for m in range(1,1000):
    assert ((m+3)//4+23)//24==(m+95)//96
print('PASS: 3 even-period fixtures, 72 reflected-orbit classes, incidence, 1 symbolic rate identity, 999 ceiling checks')
