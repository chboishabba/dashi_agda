"""Monotone bag-tree contraction, exact retained certificate and capped portfolio."""
from itertools import combinations
from random import Random
from check_pnp_affine_normal_components import canon, satisfies, cnf_flats, Budget, Exhausted
from check_pnp_collective_fibre_escape import solve as collective
from check_p0_forest_residual_20261126 import portfolio as previous, count, bound
from check_p0_affine_resolvent_20261126 import valid
from check_p0_future_safe_affine_packet_20261125 import reference


def add(Q,A,w):
    if A is not None and w:
        Q[A]=Q.get(A,0)+w
        if not Q[A]:del Q[A]


def product(A,C,B):
    Q={}
    for X,w in A.items():
        for Y,z in C.items():
            B.pay('intersection');add(Q,canon(X+Y),w*z)
    return Q


def union(A,C,B):
    Q=dict(A)
    for X,w in C.items():B.pay('union');add(Q,X,w)
    for X,w in product(A,C,B).items():add(Q,X,-w)
    return Q


def mass(n,Q,P,B):
    total=0
    for A,w in Q.items():
        B.pay('mass');total+=w*count(n,canon(P+A))
    assert total>=0
    return total


def lower(n,C,E,P,B):
    B.pay('lower');P=canon(P)
    if P is None:return 0
    return count(n,P)-sum(mass(n,Q,P,B) for Q in C.values())+sum(mass(n,Q,P,B) for Q in E.values())


def tree(n,F,B):
    C={i:{G:1} for i,G in enumerate(F)};E={};pairs=[]
    for i,j in combinations(C,2):
        B.pay('pair');Q=product(C[i],C[j],B);pairs.append((mass(n,Q,(),B),i,j,Q))
    par=list(C)
    def root(i):
        while i!=par[i]:i=par[i]
        return i
    for w,i,j,Q in sorted(pairs,key=lambda t:t[:3],reverse=True):
        B.pay('tree');a,b=root(i),root(j)
        if a!=b:par[a]=b;E[i,j]=Q
    return C,E


def candidates(n,C,E,K,limit,B):
    for i,j in sorted(E):
        B.pay('merge_candidate')
        if K[i]+K[j]>limit:continue
        Q=union(C[i],C[j],B);T={};gain=0
        for a,b in E:
            B.pay('edge_scan')
            if (a,b)==(i,j):continue
            if i not in (a,b) and j not in (a,b):T[a,b]=E[a,b];continue
            k=b if a in (i,j) else a
            key=tuple(sorted((i,k)));Z=product(Q,C[k],B)
            gain+=mass(n,Z,(),B)-mass(n,E[a,b],(),B);T[key]=Z
        assert gain>=0
        yield (gain,-K[i]-K[j],-i,-j),i,j,Q,T


def contract(n,F,limit,B,stop=True):
    """Every adjacent bag merge improves the same pointwise certificate."""
    C,E=tree(n,F,B);K={i:1 for i in C};L=lower(n,C,E,(),B)
    first=L;merges=0
    while E and (not stop or L<=0):
        best=max(candidates(n,C,E,K,limit,B),key=lambda t:t[0],default=None)
        if best is None:break
        key,i,j,Q,E=best;C[i]=Q;del C[j];K[i]+=K.pop(j)
        L+=key[0];merges+=1;B.pay('merge')
        assert L==lower(n,C,E,(),B)
    return C,E,L,first,merges


def descend(n,C,E,L,B):
    if L<=0:return None
    P=();x=0
    for i in range(n):
        Q=P+((1<<i,0),);q=lower(n,C,E,Q,B)
        if q>0:P=Q;L=q
        else:P+=((1<<i,1),);L-=q;x|=1<<i
        assert L>0
    assert L==1
    return x


def escape(n,rows,F,cap,limit=3):
    from check_pnp_affine_normal_components import restrict,lift
    B=Budget(cap)
    try:
        B.pay('input',n+len(rows)+sum(len(G)+1 for G in F)+1)
        q=restrict(n,rows,F,B)
        if q is None:return None,True
        u,V,H=q
        if () in H:return None,True
        C,E,L,_,_=contract(len(V),H,limit,B)
        x=descend(len(V),C,E,L,B)
        if x is None:return None,False
        y=lift(u,V,x);assert satisfies(y,rows,F)
        return y,True
    except Exhausted:return None,False


def portfolio(n,rows,f,cap):
    share=cap//10;F=cnf_flats(f)
    x,done=escape(n,rows,F,share)
    if done:
        if x is not None:assert valid(x,n,rows,f)
        return x,True,'bag-forest'
    try:x,_,done=collective(n,rows,F,share)
    except RecursionError:x,done=None,False
    if done:
        if x is not None:assert valid(x,n,rows,f)
        return x,True,'collective-block'
    return previous(n,rows,f,8*share)


def main():
    rng=Random(98);fixtures=points=checks=verified=empty=escapes=0
    for n in range(1,8):
        for _ in range(40):
            F=tuple(G for _ in range(rng.randrange(8)) if (G:=canon((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,n+1)))) is not None)
            B=Budget(1000000);C,E,L,first,k=contract(n,F,3,B,False)
            assert first==bound(n,F,(),B) and L>=first
            for x in range(1<<n):
                P=tuple((1<<i,x>>i&1) for i in range(n));a=lower(n,C,E,P,B)
                assert lower(n,*tree(n,F,B),P,B)<=a<=int(satisfies(x,(),F));points+=1
            for i in range(n):
                assert L==lower(n,C,E,((1<<i,0),),B)+lower(n,C,E,((1<<i,1),),B);checks+=1
            x=descend(n,C,E,L,B)
            if x is not None:assert satisfies(x,(),F);escapes+=1
            rows=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            f=[tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randrange(min(n,3)+1))) for _ in range(rng.randrange(8))]
            _,c=reference(n,rows,f);x,done,_=portfolio(n,rows,f,1000000)
            assert done and (x is not None)==bool(c)
            if c:assert valid(x,n,rows,f);verified+=1
            else:empty+=1
            fixtures+=1
    # Seven overlapping flats: singleton tree has zero bound, bag tree positive.
    for n in (4,16,32,64,128):
        F=tuple(canon(((8,0),(i,0))) for i in range(1,8));B=Budget(1000000)
        C,E,L,first,k=contract(n,F,3,B)
        assert first==0 and L>0 and k>0
        x=descend(n,C,E,L,B);assert satisfies(x,(),F)
        print('bag_control',n,'bound',L,'merges',k)
    # No inference of UNSAT from a failed certificate or exhausted cap.
    assert escape(4,(),(),0)==(None,False)
    assert escape(4,(),((),),1000)==(None,True)
    # Exercise the imported block route directly, not just an earlier portfolio exit.
    for n in (8,16,32):
        F=tuple(canon(((1,0),(2,0),(a<<2,0))) for a in range(1,13))
        x,stats,done=collective(n,(),F,1000000)
        assert done and x is not None and satisfies(x,(),F)
    print(dict(fixtures=fixtures,verified=verified,empty=empty,pointwise=points,additivity=checks,escapes=escapes,bag_controls=5,block_controls=3,controls='PASS'))

if __name__=='__main__':main()
