"""Exact affine overlap forest lower bounds and deterministic source portfolio."""
from itertools import combinations
from random import Random
from check_pnp_affine_normal_components import (
    canon, chart, lift, restrict, satisfies, cnf_flats, Budget, Exhausted)
from check_pnp_normal_transversal import transversal, reopen_core
from check_pnp_oriented_affine_elimination import eliminate, reopen, solve as oriented
from check_p0_unified_portfolio_20261126 import portfolio as previous
from check_p0_affine_resolvent_20261126 import valid
from check_p0_future_safe_affine_packet_20261125 import reference


def count(n,R):
    return 0 if R is None else 1<<(n-len(R))


def bound(n,F,P,B):
    """Max forest certificate on the exact original pinned affine fibre."""
    B.pay('base'); P=canon(P)
    if P is None:return 0
    H=[]; a=count(n,P)
    for G in F:
        B.pay('single'); R=canon(P+G)
        if R is not None:H.append(R);a-=count(n,R)
    edges=[]
    for i,j in combinations(range(len(H)),2):
        B.pay('pair'); w=count(n,canon(H[i]+H[j]))
        if w:edges.append((w,i,j))
    parent=list(range(len(H)))
    def root(i):
        while i!=parent[i]:i=parent[i]
        return i
    for w,i,j in sorted(edges,reverse=True):
        B.pay('forest');u,v=root(i),root(j)
        if u!=v:parent[u]=v;a+=w
    return a


def descend(n,F,B):
    a=bound(n,F,(),B)
    if a<=0:return None
    x=0;P=()
    for i in range(n):
        Q=P+((1<<i,0),);q=bound(n,F,Q,B)
        if q>0:P=Q;a=q
        else:
            P+=((1<<i,1),);x|=1<<i
            # Best forest on the other child is at least parent minus q.
            # No second bound query is needed for the invariant.
            a-=q;assert a>0
    assert satisfies(x,(),F)
    return x


def escape(n,required,F,cap):
    B=Budget(cap)
    try:
        B.pay('input',n+len(required)+sum(len(G)+1 for G in F)+1)
        q=restrict(n,required,F,B)
        if q is None:return None,True
        u,V,H=q;d=len(V)
        if () in H:return None,True
        # A cheap witness-only certificate before expensive core discovery.
        x=descend(d,H,B)
        if x is None:
            M,R=transversal(H,B);C=tuple(H[j] for j in R)
            k,G,history=eliminate(d,C,B)
            if () in G:return None,True
            x=descend(k,G,B)
            if x is None:return None,False
            for P,v,p in reversed(history):
                B.pay('reopen',1+sum(map(len,P)));x=reopen(P,v,p,x)
            x=reopen_core(d,H,M,R,x)
        y=lift(u,V,x);assert satisfies(y,required,F)
        return y,True
    except Exhausted:return None,False


def portfolio(n,rows,f,cap):
    """Independent bounded alternatives; UNKNOWN never becomes UNSAT."""
    F=cnf_flats(f);share=cap//8
    x,done=escape(n,rows,F,share)
    if done:
        if x is not None:assert valid(x,n,rows,f)
        return x,True,'forest-escape'
    try:x,_,done=oriented(n,rows,F,share)
    except RecursionError:x,done=None,False
    if done:
        if x is not None:assert valid(x,n,rows,f)
        return x,True,'oriented-core'
    try:return previous(n,rows,f,6*share)
    except RecursionError:return None,False,'unknown'


def main():
    rng=Random(97);checks=success=fixtures=inhabited=empty=0
    for n in range(8):
        for _ in range(50):
            F=tuple(G for _ in range(rng.randrange(8)) if (G:=canon((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,n+2)))) is not None)
            P=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            B=Budget(1000000);a=bound(n,F,P,B)
            truth=sum(satisfies(x,P,F) for x in range(1<<n));assert a<=truth
            for i in range(n):
                assert a<=bound(n,F,P+((1<<i,0),),B)+bound(n,F,P+((1<<i,1),),B);checks+=1
            x=escape(n,P,F,1000000)
            if x[1]:assert (x[0] is not None)==bool(truth)
            if x[0] is not None:assert satisfies(x[0],P,F);success+=1
            rows=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            f=[tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randrange(min(n,3)+1))) for _ in range(rng.randrange(8))]
            _,c=reference(n,rows,f);y,done,route=portfolio(n,rows,f,1000000)
            assert done and (y is not None)==bool(c)
            if c:assert valid(y,n,rows,f);inhabited+=1
            else:empty+=1
            fixtures+=1
    # Six distinct rank-two flats, common normal, full deficient core.
    # Ordinary union bound fails, overlap forest certifies two or more survivors.
    F=tuple(canon(((8,0),(i,0))) for i in range(1,7));B=Budget(100000)
    assert 16-sum(count(4,G) for G in F)==-8
    assert bound(4,F,(),B)==2 and descend(4,F,B) is not None
    M,R=transversal(F,B);assert len(R)==6 and len(M)==4
    # Full deficient core under dense invertible coordinates.
    for n in (8,12,16,20):
        A=[((1<<n)-1)^(1<<i) for i in range(n)]
        F=tuple(canon(tuple((a,0) for a in A[:n//2])+((A[i],0),(A[j],0))) for i,j in combinations(range(n//2,n),2))
        B=Budget(10000000);assert bound(n,F,(),B)>0
        x=descend(n,F,B);assert x is not None and satisfies(x,(),F)
    assert escape(4,(),(),0)==(None,False)
    assert escape(4,(),((),),1000)==(None,True)
    # A nonpositive certificate alone is not UNSAT.
    F=tuple(canon(((1<<i,0),)) for i in range(4));B=Budget(1000)
    assert bound(4,F,(),B)<=0 and satisfies(15,(),F)
    print(dict(fixtures=fixtures,verified=inhabited,empty=empty,forest_descent_checks=checks,escape_success=success,dense=4,controls='PASS'))

if __name__=='__main__':main()
