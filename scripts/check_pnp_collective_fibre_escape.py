"""Uniform signed forest fibre escape; exact collective existential reduction."""
from itertools import combinations
from random import Random
from check_pnp_affine_normal_components import (canon, chart, lift, restrict,
    simplify, satisfies, cnf_flats, Budget, Exhausted)
from check_pnp_normal_boundary_join import join
from check_pnp_normal_transversal import transversal, reopen_core
from check_pnp_oriented_affine_elimination import directions, eliminate, reopen, project


def dot(a,x): return (a&x).bit_count()%2


def coordinates(n,V):
    S=canon((v,0) for v in V);assert len(S)==len(V)
    U=[]
    for i in range(n):
        T=canon(S+((1<<i,0),))
        if len(T)>len(S):U.append(1<<i);S=T
    return U


def domain(G,d):
    return tuple((a,b) for a,b in G if a>>d==0)


def fibre(G,d,y):
    return canon((a>>d,b^dot(a&((1<<d)-1),y)) for a,b in G)


def size(G,k,pins=()):
    if G is None:return 0
    R=canon(G+pins)
    return 0 if R is None else 1<<(k-len(R))


def forest_upper(weights,edges,forced,B):
    """Max over activation supersets of forced nodes; unknown domains relaxed."""
    m=len(weights);adj=[[] for _ in weights]
    for i,j,w in edges:adj[i].append((j,w));adj[j].append((i,w))
    seen=set();total=0
    for root in range(m):
        if root in seen:continue
        seen.add(root);order=[(root,-1,0)]
        for i,p,w in order:
            for j,z in adj[i]:
                if j!=p:assert j not in seen;seen.add(j);order.append((j,i,z))
        D={}
        for i,p,w in reversed(order):
            B.pay('forest_dp');a=None if forced[i] else 0;b=weights[i]
            for j,z in adj[i]:
                if j==p:continue
                c,e=D[j]
                if a is not None:a+=e if c is None else max(c,e)
                b+=e-z if c is None else max(c,e-z)
            D[i]=(a,b)
        a,b=D[root];total+=b if a is None else max(a,b)
    return total


def certificate(n,F,V,B):
    """Return exact projected source and reopening receipt, or None (no proof)."""
    k=len(V);assert k>0;U=coordinates(n,V);d=len(U);H=set();E=[];D=[];w=[]
    B.pay('chart',n+1)
    for G in F:
        B.pay('block_scan',1+len(G))
        A=canon((sum(dot(a,v)<<i for i,v in enumerate(U+list(V))),b) for a,b in G)
        if A is None:continue
        P=domain(A,d);r=len(A)-len(P)
        if not r:H.add(P)
        else:E.append(A);D.append(P);w.append(1<<(k-r))
    forced=[not P for P in D];edges=[];upper=sum(w)
    if upper>=1<<k:
        pairs=[]
        for i,j in combinations(range(len(E)),2):
            B.pay('block_pair');P=canon(D[i]+D[j]);A=canon(E[i]+E[j])
            # Credit only overlap guaranteed on every jointly active quotient point.
            if P is not None and A is not None and domain(A,d)==P:
                z=1<<(k-len(A)+len(P));pairs.append((z,int(forced[i])+int(forced[j]),i,j))
        par=list(range(len(E)))
        def root(i):
            while i!=par[i]:i=par[i]
            return i
        for z,_,i,j in sorted(pairs,reverse=True):
            B.pay('forest_edge');a,b=root(i),root(j)
            if a!=b:par[a]=b;edges.append((i,j,z))
        upper=forest_upper(w,edges,forced,B)
    if upper>=1<<k:return None
    return tuple(sorted(H)),(tuple(U),tuple(V),tuple(E),tuple(edges),upper)


def reopen_block(receipt,y,B):
    U,V,E,edges,upper=receipt;d=len(U);k=len(V)
    G=[fibre(A,d,y) for A in E]
    pairs=[canon(G[i]+G[j]) if G[i] is not None and G[j] is not None else None for i,j,_ in edges]
    def lower(pins):
        B.pay('mass',1+len(G)+len(pairs))
        return (1<<(k-len(pins)))-sum(size(A,k,pins) for A in G)+sum(size(A,k,pins) for A in pairs)
    pins=();z=0;L=lower(pins);assert L>= (1<<k)-upper>0
    for i in range(k):
        p=pins+((1<<i,0),);q=pins+((1<<i,1),);a=lower(p);b=lower(q)
        assert a+b==L
        if a>=b:pins=p;L=a
        else:pins=q;L=b;z|=1<<i
        assert L>0
    assert L==1 and all(A is None or satisfies(z,(),(A,)) for A in G)
    return lift(lift(0,U,y),V,z)


def blocks(n,F,B):
    yield tuple(1<<i for i in range(n))
    if n<2:return
    V=[];S=()
    for v in directions(n,F,B):
        T=canon(S+((v,0),))
        if len(T)>len(S):V.append(v);S=T
    assert len(V)==n
    k=1
    while k<n:
        yield tuple(V[:k]);yield tuple(V[-k:]);k*=2


def reduce_blocks(n,F,B):
    history=[]
    while n and F and () not in F:
        for V in blocks(n,F,B):
            B.pay('block_candidate');q=certificate(n,F,V,B)
            if q is not None:
                F,receipt=q;n-=len(V);history.append(receipt);B.pay('eliminated_dimensions',len(V));break
        else:break
    return n,F,history


def solve(n,required,F,cap):
    B=Budget(cap)
    try:
        B.pay('input',n+len(required)+sum(len(G)+1 for G in F)+1)
        q=restrict(n,required,F,B)
        if q is None:return None,B.stats,True
        u,V,H=q;H=simplify(H,B);d=len(V)
        if () in H:return None,B.stats,True
        M,R=transversal(H,B);C=tuple(H[j] for j in R)
        k,G,first=reduce_blocks(d,C,B)
        k,G,mid=eliminate(k,G,B)
        k,G,last=reduce_blocks(k,G,B)
        x,_=join(k,G,B)
        if x is None:return None,B.stats,True
        for receipt in reversed(last):x=reopen_block(receipt,x,B)
        for P,v,p in reversed(mid):B.pay('reopen',1+sum(map(len,P)));x=reopen(P,v,p,x)
        for receipt in reversed(first):x=reopen_block(receipt,x,B)
        y=lift(u,V,reopen_core(d,H,M,R,x));assert satisfies(y,required,F)
        return y,B.stats,True
    except Exhausted:return None,B.stats,False


def main():
    rng=Random(369);fixtures=verified=empty=certs=points=opens=0
    for n in range(1,8):
        for _ in range(40):
            required=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            F=tuple(G for _ in range(rng.randrange(9)) if (G:=canon((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,n+1)))) is not None)
            f=[tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randrange(min(n,3)+1))) for _ in range(rng.randrange(9))]
            for H in (F,cnf_flats(f)):
                k=rng.randrange(1,n+1);V=[];S=()
                while len(V)<k:
                    v=rng.randrange(1,1<<n);T=canon(S+((v,0),))
                    if len(T)>len(S):V.append(v);S=T
                q=certificate(n,H,V,Budget(1000000))
                if q is not None:
                    P,receipt=q;U=receipt[0];certs+=1
                    for y in range(1<<len(U)):
                        a=lift(0,U,y);truth=any(satisfies(lift(a,V,t),(),H) for t in range(1<<k))
                        assert satisfies(y,(),P)==truth;points+=1
                        if truth:
                            assert satisfies(reopen_block(receipt,y,Budget(1000000)),(),H);opens+=1
                truth=[x for x in range(1<<n) if satisfies(x,required,H)]
                x,s,done=solve(n,required,H,1000000);assert done and (x is not None)==bool(truth)
                if x is not None:assert x in truth;verified+=1
                else:empty+=1
                fixtures+=1
    # Independent oracle for the relaxed activation maximization.
    for m in range(1,9):
        for _ in range(30):
            w=[rng.randrange(1,17) for i in range(m)]
            forced=[rng.randrange(3)==0 for i in range(m)]
            edges=[]
            for i in range(1,m):
                if rng.randrange(4):
                    j=rng.randrange(i);edges.append((i,j,rng.randrange(1,min(w[i],w[j])+1)))
            want=max(sum(w[i] for i in range(m) if mask>>i&1)-sum(z for i,j,z in edges if mask>>i&1 and mask>>j&1)
                     for mask in range(1<<m) if all(not f or mask>>i&1 for i,f in enumerate(forced)))
            assert forest_upper(w,edges,forced,Budget(1000000))==want
    # Forest necessary: 12 distinct rank-three flats, all share two normals.
    # Their sum of masses is 3/2, but overlap forest gives 13/16.
    F=tuple(canon(((1,0),(2,0),(a<<2,0))) for a in range(1,13))
    q=certificate(6,F,tuple(1<<i for i in range(6)),Budget(1000000));assert q is not None and q[1][-1]==52
    x=reopen_block(q[1],0,Budget(1000000));assert satisfies(x,(),F)
    # Conditional forest: eight always-active events, four active only at y=0.
    G=F[:8]+tuple(canon(A+((64,0),)) for A in F[8:])
    q=certificate(7,G,tuple(1<<i for i in range(6)),Budget(1000000));assert q is not None and q[1][-1]==52
    for y in (0,1):assert satisfies(reopen_block(q[1],y,Budget(1000000)),(),G)
    # Incompatible orientations cannot be credited as overlap.
    assert certificate(2,cnf_flats([(1,),(-1,)]),(1,2),Budget(1000)) is None
    # t=0 and t=y overlap at y=0 but jointly cover the fibre at y=1.
    assert certificate(2,(((1,0),),((3,0),)),(1,),Budget(1000)) is None
    # All possible one-dimensional directions rejected by old raw row-size cap.
    r=Random(82);n=8
    for trial in range(100):
        H=set()
        while len(H)<12:
            A=canon((r.randrange(1,1<<n),r.randrange(2)) for _ in range(4))
            if A is not None and len(A)==4:H.add(A)
        F=tuple(sorted(H));old=sum(len(A)+1 for A in F)
        M,R=transversal(F,Budget(1000000))
        if len(R)!=len(F):continue
        if all(sum(len(A)+1 for A in project(n,F,v,Budget(1000000))[0])>old for v in range(1,1<<n)):break
    else:raise AssertionError('no all-direction control')
    assert simplify(F,Budget(1000000))==F
    x,s,done=solve(n,(),F,1000000);assert done and x is not None and s['eliminated_dimensions']==n and not s['leaf_rows']
    print('all_direction_raw_growth',trial,n,old,'min_projected_rows',min(sum(len(A)+1 for A in project(n,F,v,Budget(1000000))[0]) for v in range(1,1<<n)),'charged',sum(s.values()))
    # Large full deficient cores with sparse forbidden mass, no fibre enumeration.
    for n in (16,32,64,128):
        m=n+4;k=(m+1).bit_length()+1;r=Random(n);H=set()
        while len(H)<m:
            A=canon((r.getrandbits(n),r.randrange(2)) for _ in range(k))
            if A is not None and len(A)==k:H.add(A)
        F=tuple(sorted(H));M,R=transversal(F,Budget(10000000));assert len(R)==m
        x,s,done=solve(n,(),F,10000000);assert done and x is not None and s['eliminated_dimensions']==n and not s['leaf_rows']
        print('large',n,'events',m,'charged',sum(s.values()))
    assert solve(2,(),(),0)[2] is False
    print(dict(fixtures=fixtures,verified=verified,empty=empty,certificates=certs,pointwise=points,reopens=opens,forest_dp=240,controls='PASS'))

if __name__=='__main__':main()
