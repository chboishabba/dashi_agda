"""Exact normal-space separator tables; bounded deterministic original witness producer."""
from random import Random
from itertools import combinations
from check_pnp_affine_normal_components import (canon, chart, lift, restrict, simplify,
    satisfies, cnf_flats, Budget, Exhausted, bits)

def span(A):
    return tuple(a for a,b in canon((a,0) for a in A))

def orth(n,A):
    return span(chart(n,tuple((a,0) for a in A))[1])

def intersection(n,A,C):
    return orth(n,span(orth(n,A)+orth(n,C)))

def value(A,x):
    return sum(((a&x).bit_count()%2)<<i for i,a in enumerate(A))

def rows(A,v):
    return tuple((a,(v>>i)&1) for i,a in enumerate(A))

def representative(n,A,v):
    R=canon(rows(A,v));assert R is not None
    return chart(n,R)[0]

def tree(n,F,B):
    """Greedy discovered binary tree; charge candidate cuts. No width optimality claim."""
    m=len(F);full=(1<<m)-1;U={};D={}
    def space(mask):
        if mask not in U:
            B.pay('span',1+sum(len(F[i]) for i in bits(mask)))
            U[mask]=span(a for i in bits(mask) for a,b in F[i])
        return U[mask]
    def boundary(mask):
        if mask not in D:
            B.pay('boundary');D[mask]=intersection(n,space(mask),space(full^mask))
        return D[mask]
    nodes=[(1<<i,None,None) for i in range(m)]
    while len(nodes)>1:
        best=None
        for i,j in combinations(range(len(nodes)),2):
            B.pay('candidate');mask=nodes[i][0]|nodes[j][0]
            key=(len(boundary(mask)),mask.bit_count(),mask,i,j)
            if best is None or key<best:best=key
        _,_,mask,i,j=best
        A,C=nodes[i],nodes[j];nodes.pop(j);nodes.pop(i);nodes.append((mask,A,C))
    return nodes[0],boundary,space

def join(n,F,B):
    """Every table maps boundary assignment to one feasible full-subtree receipt."""
    if not F:return 0,0
    root,boundary,space=tree(n,F,B);width=0
    def run(node):
        nonlocal width
        mask,A,C=node;D=boundary(mask);width=max(width,len(D));T={}
        if A is None:
            G=F[mask.bit_length()-1]
            B.pay('leaf_rows',1<<len(D))
            for p in range(1<<len(D)):
                pins=rows(D,p);R=canon(pins);u,V=chart(n,R)
                if not satisfies(u,(),(G,)):
                    # Within the boundary fibre, move along one direction that violates G.
                    v=next((v for v in V if any((a&v).bit_count()%2 for a,b in G)),None)
                    if v is None:continue
                    u^=v
                T[p]=rows(space(mask),value(space(mask),u))
            return T
        L=run(A);R=run(C)
        B.pay('join_pairs',len(L)*len(R))
        for l in L.values():
            for r in R.values():
                H=canon(l+r)
                if H is None:continue
                x=chart(n,H)[0];p=value(D,x)
                if p not in T:T[p]=H
        return T
    T=run(root)
    return (chart(n,T[0])[0] if 0 in T else None),width

def join_exact_one(n, row_bits, B):
    """Exact sparse boundary join of original one-hot rows on an affine chart.

    row_bits[e][j] = (normal, offset), with original bit offset XOR dot(normal,z).
    A completed empty table is exact; Budget.Exhausted is not emptiness.
    """
    from collections import defaultdict
    if not row_bits:return 0,0
    F=tuple(tuple((a,0) for a,b in G) for G in row_bits)
    root,boundary,space=tree(n,F,B);width=0
    def coordinates(A,C):
        # A may have dependent generators; C lies in its span.
        eq=tuple(value(A,1<<j) for j in range(n));out=[]
        for s in C:
            B.pay('onehot_label_map',1+n*(1+len(A)))
            H=canon((a,(s>>j)&1) for j,a in enumerate(eq))
            assert H is not None
            out.append(chart(len(A),H)[0])
        return tuple(out)
    def run(node):
        nonlocal width
        mask,A,C=node;D=boundary(mask);width=max(width,len(D));T={}
        if A is None:
            G=row_bits[mask.bit_length()-1]
            for j in range(len(G)):
                B.pay('onehot_candidate',1+len(G))
                H=canon((a,b^int(i==j)) for i,(a,b) in enumerate(G))
                if H is None:continue
                x=chart(n,H)[0];p=value(D,x)
                if p not in T:T[p]=rows(space(mask),value(space(mask),x))
        else:
            L=run(A)
            if not L:return T
            R=run(C)
            if not R:return T
            E,J=boundary(A[0]),boundary(C[0]);I=intersection(n,space(A[0]),space(C[0]))
            P,Q=coordinates(E,I),coordinates(J,I);Z=coordinates(E+J,D)
            buckets=defaultdict(list)
            for r,H in R.items():
                B.pay('onehot_hash',1+len(Q));buckets[value(Q,r)].append((r,H))
            for l,H in L.items():
                B.pay('onehot_hash',1+len(P))
                for r,K in buckets[value(P,l)]:
                    B.pay('onehot_match',1+len(Z));p=value(Z,l|(r<<len(E)))
                    if p in T:continue
                    M=canon(H+K);assert M is not None
                    assert value(D,chart(n,M)[0])==p
                    T[p]=M
                    if not D:return T # one receipt suffices for a zero boundary
        B.pay('onehot_retained',len(T));return T
    T=run(root)
    return (chart(n,T[0])[0] if 0 in T else None),width

def solve(n,required,F,cap):
    B=Budget(cap)
    try:
        B.pay('input',n+len(required)+sum(len(G)+1 for G in F)+1)
        q=restrict(n,required,F,B)
        if q is None:return None,0,B.stats,True
        u,V,H=q;H=simplify(H,B)
        if () in H:return None,0,B.stats,True
        y,w=join(len(V),H,B)
        x=None if y is None else lift(u,V,y)
        if x is not None:assert satisfies(x,required,F)
        return x,w,B.stats,True
    except Exhausted:return None,None,B.stats,False

def test_exact_one():
    rng=Random(3692611);checks=0
    for n in range(8):
        for _ in range(70):
            F=tuple(tuple((rng.randrange(1<<n),rng.randrange(2)) for j in range(rng.randrange(7))) for i in range(rng.randrange(7)))
            valid=lambda x:all(sum(b^((a&x).bit_count()%2) for a,b in G)==1 for G in F)
            truth=any(valid(x) for x in range(1<<n));x,w=join_exact_one(n,F,Budget(1000000))
            assert (x is not None)==truth and (x is None or valid(x));checks+=1
    for _ in range(400):
        m=rng.choice((3,6,9,12));n=rng.randrange(1,13)
        S=[tuple(rng.sample(range(m),3)) for i in range(n)]
        R=[sum(1<<j for j,s in enumerate(S) if i in s) for i in range(m)]
        valid=lambda x:all((x&r).bit_count()==1 for r in R)
        truth=any(valid(x) for x in range(1<<n));P=canon((r,1) for r in R)
        if P is None:x=None
        else:
            u,V=chart(n,P);F=tuple(tuple((value(V,1<<j),u>>j&1) for j in bits(r)) for r in R)
            z,w=join_exact_one(len(V),F,Budget(1000000));x=None if z is None else lift(u,V,z)
        assert (x is not None)==truth and (x is None or valid(x));checks+=1
    try:join_exact_one(1,(((1,0),),),Budget(0));assert False
    except Exhausted:pass
    for n in (8,16,32,64):
        u,V=chart(n,canon((((1<<n)-1,1),)))
        F=tuple((value(V,1<<j),u>>j&1) for j in range(n))
        x,w=join_exact_one(len(V),(F,F,F),Budget(10000000))
        assert lift(u,V,x).bit_count()==1 and w==n-1
    print('exact_one_sparse',checks,'controls PASS')

def main():
    test_exact_one()
    rng=Random(369);fixtures=verified=empty=0
    for n in range(8):
        for _ in range(40):
            required=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            F=tuple(G for _ in range(rng.randrange(7)) if (G:=canon((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,n+2)))) is not None)
            f=[tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randrange(min(n,3)+1))) for _ in range(rng.randrange(7))]
            for G in (F,cnf_flats(f)):
                truth=[x for x in range(1<<n) if satisfies(x,required,G)]
                x,w,stats,done=solve(n,required,G,1000000)
                assert done and (x is not None)==bool(truth)
                if x is not None:assert x in truth;verified+=1
                else:empty+=1
                fixtures+=1
    # Dense cycle: genuine rank-two nonlinear forbidden flats, plus affine parity controls.
    for n in (8,16,32,48):
        A=[((1<<n)-1)^(1<<i) for i in range(n)]
        G=tuple(canon(((A[i],0),(A[(i+1)%n],0))) for i in range(n))
        x,w,stats,done=solve(n,(),G,10000000)
        assert done and w==2 and x is not None and satisfies(x,(),G)
        print("nonlinear_cycle",n,"width",w,"charged",sum(stats.values()),"join_pairs",stats["join_pairs"])
        for odd in (False,True):
            F=tuple(canon(((A[i],b),(A[(i+1)%n],b^int(odd and i==n-1)))) for i in range(n) for b in (0,1))
            x,w,stats,done=solve(n,(),F,10000000)
            assert done and w<=2 and (x is not None)==(not odd)
            if x is not None:assert satisfies(x,(),F)
            print('dense_cycle',n,'inconsistent',odd,'width',w,'charged',sum(stats.values()),'join_pairs',stats['join_pairs'])
    assert solve(8,(),(),0)[3] is False
    assert solve(2,(),((),),1000)[0] is None
    # A high-rank leaf need not enumerate its full normal span.
    F=(tuple((1<<i,0) for i in range(128)),)
    x,w,s,done=solve(128,(),F,1000);assert done and x and w==0
    print(dict(fixtures=fixtures,verified=verified,empty=empty,dense_cycles=12,high_rank_leaf=1,controls='PASS'))
if __name__=='__main__':main()
