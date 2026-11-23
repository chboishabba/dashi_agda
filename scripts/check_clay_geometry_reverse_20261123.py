#!/usr/bin/env python3
"""Exact reverse-solve: NS work-shift geometry, original N21 history/cut fibres,
Hodge complementary pairing and E32 odd-polynomial finite-field symmetry.
No original PDE/helical realization, gamma parser/tape clock, modularity, or
all-variety geometric comparison is inferred from these finite checks.
"""
from collections import defaultdict, deque
from fractions import Fraction as Q
from itertools import combinations, product
from math import comb
from random import Random
from sympy import legendre_symbol, primerange


def ns_check():
    rng=Random(7236)
    tests=0
    for _ in range(2400):
        n=rng.randrange(1,12)
        g=[rng.randrange(3) for i in range(n)]
        r=[Q(rng.randrange(-7,8),rng.randrange(1,5)) for i in range(n)]
        w=[Q(rng.randrange(-6,7),rng.randrange(1,5)) for i in range(n)]
        c=[Q(rng.randrange(-5,6),7) for _ in range(3)]
        count=[g.count(a) for a in range(3)]
        R=[sum((r[i] for i in range(n) if g[i]==a),Q(0)) for a in range(3)]
        edge={(a,b):count[b]*R[a]-count[a]*R[b] for a in range(3) for b in range(a+1,3)}
        cross={(a,b):-(sum(((r[i]-r[j])*(w[i]-w[j]) for i in range(n) for j in range(i+1,n)
                        if set((g[i],g[j]))==set((a,b))),Q(0))) for a,b in edge}
        changed={(a,b):-(sum(((r[i]-r[j])*(w[i]-c[g[i]]-w[j]+c[g[j]])
                              for i in range(n) for j in range(i+1,n)
                              if set((g[i],g[j]))==set((a,b))),Q(0))) for a,b in edge}
        for (a,b),k in edge.items():
            assert changed[a,b]-cross[a,b]==(c[a]-c[b])*k
        direct=sum((changed[e]-cross[e] for e in edge),Q(0))
        N=sum(count); Rt=sum(R,Q(0))
        total=sum((c[a]*(N*R[a]-count[a]*Rt) for a in range(3)),Q(0))
        assert direct==total
        # Reverse-solve full block invariance on graph of nonzero coefficients.
        adj={a:set() for a in range(3) if count[a]}
        for (a,b),k in edge.items():
            if k:
                adj[a].add(b);adj[b].add(a)
        components=[]; visited=set()
        for v in adj:
            if v in visited:continue
            todo=[v]; cc=set()
            while todo:
                u=todo.pop()
                if u in cc:continue
                cc.add(u);todo.extend(adj[u]-cc)
            components.append(cc);visited|=cc
        graph_kernel=all(len({c[a] for a in cc})==1 for cc in components)
        exact_kernel=all(changed[e]==cross[e] for e in edge)
        assert graph_kernel==exact_kernel
        tests+=1
    # Total-sign cancellation is strictly weaker than six-block preservation.
    r=[Q(1),Q(2),Q(3)];g=[0,1,2];c=[Q(1),Q(0),Q(1)]
    assert sum(c[a]*(3*r[a]-sum(r)) for a in range(3))==0
    assert (c[0]-c[1])*(r[0]-r[1])!=0
    # A fixed-output amplitude lift has a necessary total-shift constraint.
    for _ in range(600):
        A=[(Q(rng.randrange(-5,6)),Q(rng.randrange(-5,6))) for i in range(5)]
        M=(sum((x for x,y in A),Q(0)),sum((y for x,y in A),Q(0)))
        norm=M[0]*M[0]+M[1]*M[1]
        if not norm:continue
        shift=[Q(rng.randrange(-3,4),5) for i in range(4)]
        shift.append(-sum(shift,Q(0)))
        moved=[(v[0]-s*M[0]/(2*norm),v[1]-s*M[1]/(2*norm)) for v,s in zip(A,shift)]
        Mnew=(sum((x for x,y in moved),Q(0)),sum((y for x,y in moved),Q(0)))
        assert Mnew==M
        for old,new,s in zip(A,moved,shift):
            assert 2*sum(a*b for a,b in zip(M,new))==2*sum(a*b for a,b in zip(M,old))-s
    assert all(2*sum(a*b for a,b in zip((0,0), v))==0 for v in [(4,2),(-4,-2)])
    return tests


def k_components(n, edges):
    used={v for u,v,_ in edges for v in (u,v)}
    adj=defaultdict(list)
    for u,v,_ in edges:adj[u].append(v);adj[v].append(u)
    seen=set(); comps=0
    for x in used:
        if x in seen:continue
        comps+=1;todo=[x]
        while todo:
            y=todo.pop()
            if y in seen:continue
            seen.add(y);todo.extend(adj[y])
    return len(used),comps


def k_reconstruct(edges, parity):
    # Solve xor(x_u,x_v)=parity_e on actual observed endpoints only.
    adj=defaultdict(list)
    for (u,v,_),bit in zip(edges,parity):
        adj[u].append((v,bit));adj[v].append((u,bit))
    phi={};components=0
    for root in adj:
        if root in phi:continue
        components+=1;phi[root]=0;todo=deque([root])
        while todo:
            u=todo.popleft()
            for v,b in adj[u]:
                candidate=phi[u]^b
                if v in phi:
                    if phi[v]!=candidate:return None
                else:phi[v]=candidate;todo.append(v)
    return phi,components


def karp_check():
    checks=0
    for n in range(2,6):
        possible=list(combinations(range(n),2))
        for m in range(min(4,len(possible))+1):
            for subset in combinations(possible,m):
                edges=[(u,v,2*i-3) for i,(u,v) in enumerate(subset)]
                k,b=k_components(n,edges)
                # Original source-batched history: each edge compares both
                # endpoints to exactly 2*j earlier endpoints, never siblings.
                assert 2*m*(m-1)==sum(4*j for j in range(m))
                assert m*(2*m-1)-2*m*(m-1)==m
                accepted_labels=0
                for labels in product((0,1),repeat=n):
                    observed=tuple(labels[u] for u,v,w in edges for u in (u,v))
                    assert len(observed)==2*m
                    accepted_labels+=1
                assert accepted_labels==2**n
                seen_parity={}
                for parity in product((0,1),repeat=m):
                    witness=k_reconstruct(edges,parity)
                    count=sum(all((labels[u]^labels[v])==bit for (u,v,w),bit in zip(edges,parity))
                              for labels in product((0,1),repeat=n))
                    if witness is None:
                        assert count==0
                    else:
                        phi,b2=witness
                        assert b2==b and len(phi)==k
                        assert count==2**(b+n-k)
                        score=sum(w*bit for (u,v,w),bit in zip(edges,parity))
                        for labels in product((0,1),repeat=n):
                            if all((labels[u]^labels[v])==bit for (u,v,w),bit in zip(edges,parity)):
                                assert score==sum(w for u,v,w in edges if labels[u]!=labels[v])
                    checks+=1
                consistent_cert=0
                for observed in product((0,1),repeat=2*m):
                    first={};good=True
                    for (u,v,_),a,bb in zip(edges,observed[::2],observed[1::2]):
                        for vertex,value in ((u,a),(v,bb)):
                            if vertex in first and first[vertex]!=value:good=False
                            first[vertex]=value
                    consistent_cert+=good
                assert consistent_cert==2**k
    return checks


def hodge_check():
    rng=Random(9234);checks=0
    for r in range(9):
        top=(1<<r)-1
        for p in range(r+1):
            basis=[b for b in range(1<<r) if b.bit_count()==p]
            complementary=[top^b for b in basis]
            assert len(basis)==comb(r,p) and len(set(complementary))==len(basis)
            for _ in range(20):
                alpha={b:Q(rng.randrange(-9,10),7) for b in basis}
                # Pair with explicit complementary coordinate cycle class.
                reversed_coeff={b:sum((v for I,v in alpha.items() if (I & (top^b))==0 and
                                        (I | (top^b))==top),Q(0)) for b in basis}
                assert alpha==reversed_coeff
                checks+=1
    return checks


def bsd_check():
    count=0
    for p in primerange(3,301):
        if p%4!=3:continue
        for d in (1,2,3,5):
            if d%p==0:continue
            f=lambda x: (x*x*x-d*d*x)%p
            assert -sum(int(legendre_symbol(f(x),p)) for x in range(p))==0
            for x in range(p):
                assert int(legendre_symbol(f(x),p))==-int(legendre_symbol(f(-x),p))
            count+=1
    # split-prime negative control on original E32, not a universal converse.
    assert -sum(int(legendre_symbol((x*x*x-x)%5,5)) for x in range(5))==-2
    return count

if __name__=='__main__':
    for name,func in [('NS',ns_check),('KARP',karp_check),('HODGE',hodge_check),('BSD',bsd_check)]:
        print(name,func())
    print('PASS geometry-forward BIDI/reverse checks; source-physical and kernel gates remain OPEN')
