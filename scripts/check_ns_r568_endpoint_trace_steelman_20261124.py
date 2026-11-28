#!/usr/bin/env python3
"""Exact R568 cutoff-one incidence, Cauchy Gram time-polynomial and endpoint
BIDI regression. Polynomial M/D is an abstract source-type path, NOT a
physical NS Galerkin trajectory. Physical time-zero source tests live in
check_ns_r568_physical_source_weld_exact_20261123.py.
"""
from itertools import product
from collections import Counter, defaultdict
import sympy as s

t=s.symbols('t',real=True)
T=s.Rational(2,3)
k=(1,0,0)
pairs=[]
for p in product(range(-1,2),repeat=3):
    q=tuple(k[i]-p[i] for i in range(3))
    if all(-1<=v<=1 for v in q):
        pairs.append((p,q,sum(a*a+b*b for a,b in zip(p,q))))
assert len(pairs)==18 and Counter(r for _,_,r in pairs)=={1:2,3:8,5:8}

def vdata(idx):
    # Three complex components, each represented as a real/imaginary pair.
    return tuple((s.Integer((idx*(j+2)+j)%7-3)+s.Integer((idx+j)%3-1)*t,
                  s.Integer((idx*(j+1)+2*j)%5-2)*t+s.Rational((idx+j)%4-2,2))
                 for j in range(3))

def vadd(u,v):
    return tuple((a+c,b+d) for (a,b),(c,d) in zip(u,v))

def inner(u,v):
    return sum((a*c+b*d for (a,b),(c,d) in zip(u,v)),s.Integer(0))

zero=tuple((s.Integer(0),s.Integer(0)) for _ in range(3))
rows=[]
for i,(_,_,r) in enumerate(pairs):
    M=vdata(i+1)
    D=tuple((s.diff(a,t)+r*a,s.diff(b,t)+r*b) for a,b in M)
    rows.append((r,M,D))
def full(currency):
    return s.expand(sum((inner((m if currency=='Q' else d),n)/(r+rr)
                         for r,m,d in rows for rr,n,dd in rows),s.Integer(0)))
bucket=defaultdict(lambda:(zero,zero))
for r,M,D in rows:
    a,b=bucket[r]
    bucket[r]=(vadd(a,M),vadd(b,D))
Qdirect=full('Q')
Fdirect=full('F')
Qbucket=s.expand(sum((inner(m,n)/(r+rr) for r,(m,d) in bucket.items()
                       for rr,(n,dd) in bucket.items()),s.Integer(0)))
Fbucket=s.expand(sum((inner(d,n)/(r+rr) for r,(m,d) in bucket.items()
                       for rr,(n,dd) in bucket.items()),s.Integer(0)))
assert s.expand(Qdirect-Qbucket)==0
assert s.expand(Fdirect-Fbucket)==0
Msum=zero
for _,M,_ in rows:
    Msum=vadd(Msum,M)
H=s.expand(inner(Msum,Msum))
assert s.expand(s.diff(Qdirect,t)-(2*Fdirect-H))==0
Qsource=2*Qdirect
lhs=s.integrate(4*Fdirect,(t,0,T))
trace=s.integrate(2*H,(t,0,T))
delta=s.expand(Qsource.subs(t,T)-Qsource.subs(t,0))
assert s.expand(lhs-delta-trace)==0
assert Qsource.subs(t,0)>0 and Qsource.subs(t,T)>0 and trace>0
for gap,expected in ((s.Rational(3,7),True),(-s.Rational(1,11),False)):
    B=lhs+gap
    assert bool(lhs<=B)==bool(Qsource.subs(t,T)+trace<=B+Qsource.subs(t,0))==expected
# Wrong 1x-vs-2x coherent-work factor must be rejected.
assert delta!=0
assert s.expand(lhs-(Qdirect.subs(t,T)-Qdirect.subs(t,0))-trace)!=0
counts=Counter()
for C in (1,2):
    for kk in product(range(-C,C+1),repeat=3):
        if kk==(0,0,0):continue
        for p in product(range(-C,C+1),repeat=3):
            q=tuple(kk[i]-p[i] for i in range(3))
            if not all(-C<=x<=C for x in q):continue
            mass=sum(a*a+b*b for a,b in zip(p,q))
            assert 2*mass>=sum(x*x for x in kk)
            counts[C]+=1
assert counts[1]>0 and counts[2]>counts[1]
print('PASS 18 original C=1 incidences; masses 1:2,3:8,5:8')
print('PASS exact direct/rate-bucket Q,F polynomials and Qprime=2F-H')
print('PASS exact forward integral/reverse terminal budget, both truth directions')
print('PASS wrong-factor negative control and midpoint bound C=1,2')
print('Qsource(0), Qsource(T), trace, 4 int F =',
      Qsource.subs(t,0),Qsource.subs(t,T),trace,lhs)
print('OPEN: physical time/source R240, native FTC/real field, C1/C2 and 3D PDE')
