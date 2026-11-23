#!/usr/bin/env python3
"""Exact original NS R568 p+q=k rate geometry / Cauchy radical regression.

Reuses original PhysicalTriadIncidence p,q,k geometry, INCLUDING k itself bounded by C, and input decay mass.
All D/M here are independently assigned rational three-vector PROXIES:
not the original Galerkin nonlinear force. This is finite algebra only.
"""
from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import product
from random import Random

ZERO = (Q(0), Q(0), Q(0))
def squared(p): return sum(x*x for x in p)
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def scale(a,c): return tuple(c*x for x in a)
def dot(a,b): return sum((x*y for x,y in zip(a,b)),Q(0))
def fibre(C,k):
    return [(p,tuple(k[i]-p[i] for i in range(3)))
            for p in product(range(-C,C+1),repeat=3)
            if all(abs(k[i]-p[i])<=C for i in range(3))]
def mass(pair): return squared(pair[0])+squared(pair[1])
def midpoint_fibre(C,k):
    b=[2*C-abs(x) for x in k]
    if min(b)<0: return []
    return [(tuple((k[i]+d[i])//2 for i in range(3)),
             tuple((k[i]-d[i])//2 for i in range(3)))
            for d in product(*(range(-v,v+1) for v in b))
            if all((d[i]-k[i])%2==0 for i in range(3))]
def rate_polynomial(C,k):
    """Exact product of 1D source incidence polynomials; coefficient=rate multiplicity."""
    P=Counter({0:1})
    for ki in k:
        b=2*C-abs(ki)
        if b<0:return Counter()
        A=Counter()
        for di in range(-b,b+1):
            if (di-ki)%2==0:A[(ki*ki+di*di)//2]+=1
        P=Counter({m+n:sum(a*b for r,a in P.items() for s,b in A.items()
                             if r+s==m+n) for m in P for n in A})
    return P
def classes(v):
    groups=defaultdict(list)
    for key,value in v.items():groups[mass(key)].append((key,value))
    return groups
def aggregated(v):
    return {m:tuple(sum((x[i] for _,x in members),Q(0)) for i in range(3))
            for m,members in classes(v).items()}
def projector(v):
    out={}
    for members in classes(v).values():
        mean=tuple(sum((x[i] for _,x in members),Q(0))/len(members)
                   for i in range(3))
        for key,_ in members:out[key]=mean
    return out
def force(A,B):
    a=aggregated(A);b=aggregated(B)
    return sum((dot(x,y)/Q(m+n) for m,x in a.items() for n,y in b.items()),Q(0))
def det(M):
    M=[list(row) for row in M];n=len(M);out=Q(1)
    for j in range(n):
        t=next((i for i in range(j,n) if M[i][j]),None)
        if t is None:return Q(0)
        if t!=j:M[j],M[t]=M[t],M[j];out=-out
        pivot=M[j][j];out*=pivot
        for i in range(j+1,n):
            f=M[i][j]/pivot
            for h in range(j+1,n):M[i][h]-=f*M[j][h]
            M[i][j]=Q(0)
    return out
def run():
    rng=Random(20261123);tested=0;incidences=0;rank_checks=0;direct_checks=0
    for C in range(1,7):
        for k in [(1,0,0),(1,1,0),(2,0,0),(2,1,1),
                  (3,0,0),(3,2,1),(5,0,0),(0,0,2)]:
            if max(abs(x) for x in k)>C:continue
            items=fibre(C,k);same=midpoint_fibre(C,k);N=len(items)
            assert len(same)==N and set(same)==set(items)
            poly=rate_polynomial(C,k)
            assert poly==Counter(mass(t) for t in items)
            assert sum(poly.values())==N
            lo=(squared(k)+sum(abs(x)%2 for x in k))//2
            hi=(squared(k)+sum((2*C-abs(x))**2 for x in k))//2
            R=sorted(poly)
            assert len(R)<=(hi-lo)//2+1<=3*C*C+1
            assert all((m-lo)%2==0 for m in R)
            swap=(lambda t:(t[1],t[0]))
            for p,q in items:
                d=tuple(p[i]-q[i] for i in range(3))
                assert sum(k[i]*k[i]+d[i]*d[i] for i in range(3))==2*mass((p,q))
                assert all(abs(d[i])<=2*C-abs(k[i]) for i in range(3))
                assert all((d[i]-k[i])%2==0 for i in range(3))
                assert mass((p,q))%2==squared(k)%2
            fixed=int(all(x%2==0 for x in k))
            assert sum(p==q for p,q in items)==fixed
            assert (N-fixed)%2==0
            def randvec():
                return tuple(Q(rng.randrange(-3,4),rng.randrange(1,5))
                             if rng.randrange(3)==0 else Q(0) for _ in range(3))
            A={t:randvec() for t in items}
            B={t:randvec() for t in items}
            Ae={t:scale(add(A[t],A[swap(t)]),Q(1,2)) for t in items}
            Be={t:scale(add(B[t],B[swap(t)]),Q(1,2)) for t in items}
            Ao={t:sub(A[t],Ae[t]) for t in items}
            Bo={t:sub(B[t],Be[t]) for t in items}
            assert all(Ao[swap(t)]==scale(Ao[t],-1) for t in items)
            assert all(Bo[swap(t)]==scale(Bo[t],-1) for t in items)
            assert all(x==ZERO for x in aggregated(Ao).values())
            assert all(x==ZERO for x in aggregated(Bo).values())
            f=force(A,B)
            assert f==force(Ae,Be)==force(Ae,B)==force(A,Be)
            assert force(Ao,B)==force(A,Bo)==force(Ao,Bo)==0
            Ap=projector(A);Bp=projector(B)
            assert projector(Ap)==Ap and projector(Bp)==Bp
            assert force(Ap,Bp)==force(Ap,B)==force(A,Bp)==f
            assert aggregated(Ap)==aggregated(A) and aggregated(Bp)==aggregated(B)
            if N<=128:
                direct=sum((dot(A[t],B[u])/Q(mass(t)+mass(u))
                            for t in items for u in items),Q(0))
                assert direct==f;direct_checks+=1
            if len(R)<=8:
                Cauchy=[[Q(1,m+n) for n in R] for m in R]
                numerator=1
                for i,m in enumerate(R):
                    for n in R[i+1:]: numerator*=(n-m)**2
                denominator=1
                for m in R:
                    for n in R: denominator*=m+n
                assert det(Cauchy)==Q(numerator,denominator)>0
                rank_checks+=1
            if k==(5,0,0) and C in (3,4,5,6):
                print('k=(5,0,0)', 'C=',C,'incidences=',N,
                      'Cauchy-rank=',len(R),'radical-dim=',N-len(R),
                      'parity-ceiling=',(hi-lo)//2+1)
            tested+=1;incidences+=N
    assert tested==37
    assert incidences==26934
    assert direct_checks==8 and rank_checks==4
    print('PASS',tested,'full real-source lattice fibres,',incidences,'incidence checks')
    print('PASS 1D polynomial multiplicities, exact midpoint BIDI, swap-odd null')
    print('PASS both-currency exact projector,',rank_checks,'strict Cauchy determinant cases')
    print('PASS',direct_checks,'independent literal O(N^2) rational pair evaluations')
    print('UNPAID: original physical doubleForcing/doubleCell realization, analytic C1/C2, native Agda/Lean proof')
if __name__=='__main__':run()
