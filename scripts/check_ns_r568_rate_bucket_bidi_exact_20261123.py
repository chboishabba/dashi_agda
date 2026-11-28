#!/usr/bin/env python3
"""Original fixed-output cubic p+q=k incidence, R541/R567/R687 Cauchy scalarization.

D_a and M_a are independent rational VECTOR test carriers for original
doubleForcing / doubleCell; not inferred from a physical Galerkin trajectory.
This checks finite signed algebra and reversible rate grouping ONLY.
"""
from fractions import Fraction as Q
from itertools import product
from random import Random

Z=(Q(0),Q(0),Q(0))
def dot(a,b):return sum((u*v for u,v in zip(a,b)),Q(0))
def plus(a,b):return tuple(x+y for x,y in zip(a,b))
def fibre(C,k):
    for p in product(range(-C,C+1),repeat=3):
        q=tuple(k[i]-p[i] for i in range(3))
        if all(-C<=v<=C for v in q):
            yield p,q,sum(t*t for t in p)+sum(t*t for t in q)
def kernel(a,b):
    return Q(1,a+b) if a+b else Q(0)
def sumdot(rows):
    D=Z;M=Z
    for _,_,_,d,m in rows:D=plus(D,d);M=plus(M,m)
    return dot(D,M)
def direct(rows):
    # Exact scalar evaluation may omit zero VECTOR factors, not stored rows.
    ds=[(r,d) for _,_,r,d,m in rows if d!=Z]
    ms=[(r,m) for _,_,r,d,m in rows if m!=Z]
    return sum((kernel(r,s)*dot(d,m) for r,d in ds for s,m in ms),Q(0))
def grouping(rows):
    groups={}
    for index,(p,q,r,d,m) in enumerate(rows):
        if r not in groups:groups[r]=[Z,Z,[]]
        g=groups[r];g[0]=plus(g[0],d);g[1]=plus(g[1],m)
        g[2].append((index,p,q,d,m))
    return groups
def grouped(rows):
    g=grouping(rows)
    return sum((kernel(r,s)*dot(a[0],b[1]) for r,a in g.items() for s,b in g.items()),Q(0))
def withcurr(C,k,carriers):
    return [(p,q,r,*carriers.get((p,q),(Z,Z))) for p,q,r in fibre(C,k)]
def run():
    k=(5,0,0)
    a=((2,0,0),(3,0,0));b=((1,0,0),(4,0,0))
    carriers={a:((Q(1),Q(0),Q(0)),(Q(1),Q(0),Q(0))),
              b:((Q(-11,10),Q(0),Q(0)),(Q(1),Q(0),Q(0)))}
    selected=[row for row in withcurr(5,k,carriers) if (row[0],row[1]) in carriers]
    assert {r for _,_,r,_,_ in selected}=={13,17}
    F=direct(selected);L=sumdot(selected)
    assert F==Q(46,16575)>0 and L==-Q(1,5)<0 and grouped(selected)==F
    determinant=kernel(13,13)*kernel(17,17)-kernel(13,17)**2
    assert determinant==Q(1,49725)>0
    for nu in [Q(1,3),Q(1),Q(2),Q(5,2)]:
        scaled=[(p,q,nu*r,d,m) for p,q,r,d,m in selected]
        assert direct(scaled)==grouped(scaled)==F/nu and sumdot(scaled)==L
    for C in (5,6,7):
        rows=withcurr(C,k,carriers)
        assert direct(rows)==grouped(rows)==F and sumdot(rows)==L
        assert len(rows)==(2*C-5+1)*(2*C+1)**2
        g=grouping(rows)
        assert len(g)<=6*C*C+1
        back=sorted((i,p,q,r,d,m) for r,v in g.items() for i,p,q,d,m in v[2])
        assert back==[(i,*row) for i,row in enumerate(rows)]
        print('PASS padded cutoff',C,'incidences',len(rows),'rate classes',len(g))
    # One-currency zero is NOT pair-inert.
    arow=next(row for row in selected if row[2]==13)
    lone=[arow,(b[0],b[1],17,(Q(1),Q(0),Q(0)),Z)]
    assert direct(lone)==Q(1,26)+Q(1,30)!=direct([arow])
    rng=Random(20261123)
    trials=0;maxn=0
    for C in range(1,5):
        for k in [(1,0,0),(1,1,0),(2,1,1),(3,0,0),(0,2,1)]:
            if max(map(abs,k))>C:continue
            raw=list(fibre(C,k))
            assert all(0<r<=6*C*C for _,_,r in raw)
            for _ in range(4):
                def vec():
                    return tuple(Q(rng.randrange(-3,4),rng.randrange(1,5))
                                 if rng.randrange(4)==0 else Q(0) for _ in range(3))
                rows=[(p,q,r,vec(),vec()) for p,q,r in raw]
                assert direct(rows)==grouped(rows)
                maxn=max(maxn,len(rows));trials+=1
    assert trials==64
    print('PASS',trials,'full ordered source-fibre rational tests; max incidences',maxn)
    print('PASS actual-lattice two-rate algebraic sign obstruction F=',F,'L=',L,'Cauchy determinant=',determinant)
    print('BOUNDARY: free D/M rational carriers, NOT a Galerkin solution or R568 spacetime proof')
if __name__=='__main__':run()
