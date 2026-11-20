"""Literal ordered-axis Path13 contour incidence, before wrap; exact arithmetic.
Counts unsigned path occurrences, not the true signed matrix coefficients.
"""
from collections import Counter
from itertools import product
import sympy as s
L=13; N=L**4; Z=(0,)*4

def walk(start,offset):
    x=list(start)
    for d,n in enumerate(offset):
        for _ in range(abs(n)):
            if n<0: x[d]-=1
            yield (tuple(x),d)
            if n>0: x[d]+=1

def shift(x,mu):
    return tuple(a+L*(k==mu) for k,a in enumerate(x))

minus=Counter()
cross=[Counter() for _ in range(4)]
for x in product(range(-6,7),repeat=4):
    minus.update(walk(Z,x))
    for mu in range(4):
        cross[mu].update(walk(x,shift(Z,mu)))
assert sum(minus.values())==4*42*L**3
for (x,d),v in minus.items():
    k=x[d]; count=6-k if k>=0 else k+7
    assert all(a==0 for a in x[d+1:])
    assert v==count*L**(3-d)
rows=[]; folded=Counter(); support=Counter()
for mu in range(4):
    centre=Counter(walk(Z,shift(Z,mu)))
    plus=Counter({(shift(x,mu),d):v for (x,d),v in minus.items()})
    C=minus+plus+cross[mu]+Counter({e:N*v for e,v in centre.items()})
    assert sum(C.values())==674*L**3
    rows.append(C)
    for (x,d),v in C.items():
        key=(tuple(a%L for a in x),d)
        folded[key]+=v;support[key]+=1
maxcol=max(folded.values()); maxsupport=max(support.values())
assert maxcol==N*1+13+8*6*L**3
assert maxsupport<=12
print('row mean',s.Rational(sum(rows[0].values()),N),'max raw folded column',maxcol,'normalized',s.Rational(maxcol,N),'max row support overlaps',maxsupport)
print('per-axis maxima', [max(v for (x,d),v in folded.items() if d==k) for k in range(4)])
print('PASS literal contour incidence')
