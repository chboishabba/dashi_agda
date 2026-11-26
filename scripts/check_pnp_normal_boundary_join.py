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

def onehot_exclusion_core(n,G,H,B):
    """Certified weaker empty demand for a single exact-one row, or None.

    H is a consistent canonical demand. Return a conjunction entailed by H,
    inconsistent with every original one-hot pattern, not just a rank test.
    """
    D=intersection(n,span(a for a,b in H),span(a for a,b in G))
    target=value(D,chart(n,H)[0]);diff=set()
    for j in range(len(G)):
        B.pay('core_pattern',1+len(G)+len(D))
        Q=canon((a,b^int(i==j)) for i,(a,b) in enumerate(G))
        if Q is None:continue
        v=value(D,chart(n,Q)[0])^target
        if not v:return None
        diff.add(v)
    out=[];full=(1<<len(D))-1
    while diff:
        p=0
        # Conditional expectation: choose a parity detecting >= half the
        # nonzero differences, without enumerating the dual space.
        for j in range(len(D)):
            rest=full^((1<<(j+1))-1)
            def score(q):
                B.pay('core_parity',len(diff))
                return sum(1 if v&rest else 2*((v&q).bit_count()%2) for v in diff)
            if score(p|(1<<j))>score(p):p|=1<<j
        nxt={v for v in diff if not (v&p).bit_count()%2}
        assert 2*len(nxt)<=len(diff) and p
        out.append((lift(0,D,p),(p&target).bit_count()%2));diff=nxt
    E=canon(out);assert E is not None and canon(H+E)==H
    return E

def cached_empty_cover(n,H,empty,B,limit):
    """Sound collective coverage of a demand by completed empty fibres only."""
    if limit<=0 or not empty:return False
    F=tuple(empty[-limit:]);B.pay('demand_cover_input',1+len(H)+sum(1+len(E) for E in F))
    q=restrict(n,H,F,B)
    if q is None:return True
    _,_,G=q
    return () in simplify(G,B)


def join_exact_one_demand(n, row_bits, B, required=(), core_trials=0, core_cover=0):
    """Find one original exact-one receipt, with affine demand in the row span.

    No dense/full boundary table is required. Memoize only completed queries.
    Budget exhaustion propagates (not an empty fibre).
    """
    assert core_trials>=0 and core_cover>=0
    H=canon(required)
    if H is None:return None,0
    if not row_bits:
        assert not H
        return 0,0
    F=tuple(tuple((a,0) for a,b in G) for G in row_bits)
    root,_,space=tree(n,F,B);memo={};empty={};maps={};width=0
    assert span(space(root[0])+tuple(a for a,b in H))==space(root[0])
    def structure(A,C):
        key=(A[0],C[0])
        if key not in maps:
            U,V=space(A[0]),space(C[0]);I=intersection(n,U,V)
            E=U+V;eq=tuple(value(E,1<<j) for j in range(n))
            maps[key]=(U,V,I,eq)
        return maps[key]
    def remember_empty(mask,H):
        empty.setdefault(mask,[]).append(H)
    def ask(node,H,learn=True):
        nonlocal width
        key=(node[0],H);B.pay('demand_query',1+len(H))
        if key in memo:B.pay('demand_cache');return memo[key]
        mask,A,C=node;out=None
        for E in empty.get(mask,()):
            B.pay('demand_subsumption',1+len(E)+len(H))
            if canon(H+E)==H:
                B.pay('demand_core_hit');return None
        if cached_empty_cover(n,H,empty.get(mask,()),B,core_cover):
            B.pay('demand_collective_hit');memo[key]=None;remember_empty(mask,H);return None
        if A is None:
            G=row_bits[mask.bit_length()-1]
            for j in range(len(G)):
                B.pay('demand_leaf',1+len(G)+len(H))
                K=canon(H+tuple((a,b^int(i==j)) for i,(a,b) in enumerate(G)))
                if K is not None:
                    out=rows(space(mask),value(space(mask),chart(n,K)[0]));break
        else:
            # Enumerate only the left projection needed for this demand.
            if A[0].bit_count()>C[0].bit_count():A,C=C,A
            U,V,I,eq=structure(A,C);L=[];R=[]
            for s,b in H:
                B.pay('demand_map',1+n*(1+len(U)+len(V)))
                K=canon((a,s>>j&1) for j,a in enumerate(eq));assert K is not None
                p=chart(len(U)+len(V),K)[0]
                L.append(lift(0,U,p&((1<<len(U))-1)))
                R.append((lift(0,V,p>>len(U)),b))
            # Linear consistency of the right demand pulls back to left pins.
            A0=I+tuple(L);B0=I+tuple(r for r,b in R)
            rhs=sum(b<< (len(I)+j) for j,(r,b) in enumerate(R))
            relations=chart(len(B0),canon((value(B0,1<<j),0) for j in range(n)))[1]
            B.pay('demand_linear_projection',1+len(B0)*(n+len(relations)))
            pins=canon((lift(0,A0,v),(v&rhs).bit_count()%2) for v in relations)
            if pins is None:
                memo[key]=None;remember_empty(mask,H);return None
            # Fixed pins plus independent free normals determine the entire
            # right demand; never branch on a pinned observation coordinate.
            basis=span(a for a,b in pins);P=[]
            for s in span(A0):
                C0=span(basis+(s,))
                if len(C0)>len(basis):P.append(s);basis=C0
            width=max(width,len(P));todo=[pins]
            # B0 may be dependent: select a coefficient representation for
            # each right demand normal. All choices agree on the left pins.
            eq0=tuple(value(B0,1<<j) for j in range(n));pull={}
            while todo:
                Hleft=todo.pop();B.pay('demand_prefix',1+len(Hleft))
                X=ask(A,Hleft,learn)
                if X is None:continue
                x=chart(n,canon(X))[0]
                K=canon(rows(I,value(I,x))+tuple((r,b^((l&x).bit_count()%2)) for l,(r,b) in zip(L,R)))
                assert K is not None
                Y=ask(C,K,learn)
                if Y is not None:
                    out=canon(X+Y);assert out is not None
                    z=chart(n,out)[0]
                    assert all((s&z).bit_count()%2==b for s,b in H)
                    break
                # Compress a completed empty demand using original row
                # conflicts, optionally followed by bounded deletion probes.
                E=K
                if learn:
                    for i in bits(C[0]):
                        B.pay('core_row')
                        E0=onehot_exclusion_core(n,row_bits[i],K,B)
                        if E0 is not None and len(E0)<len(E):E=E0
                        if not E:break
                    for row in E[:core_trials]:
                        if row not in E:continue
                        C0=tuple(q for q in E if q!=row)
                        B.pay('demand_core_probe',1+len(C0))
                        if ask(C,C0,False) is None:
                            E=C0;B.pay('demand_core_drop')
                if E!=K:remember_empty(C[0],E)
                F0=[]
                for s,b in E:
                    if s not in pull:
                        B.pay('demand_core_map',1+n*(1+len(B0)))
                        Q=canon((a,s>>j&1) for j,a in enumerate(eq0));assert Q is not None
                        v=chart(len(B0),Q)[0]
                        pull[s]=(lift(0,A0,v),(v&rhs).bit_count()%2)
                    l,c=pull[s];F0.append((l,b^c))
                F0=canon(F0);assert F0 is not None and satisfies(x,F0,())
                # Exact disjoint affine subtraction Hleft \ F0. A row
                # already implied by Hleft contributes no sibling.
                Q=Hleft;children=[]
                for l,b in F0:
                    B.pay('demand_split')
                    other=canon(Q+((l,b^1),))
                    if other is not None:children.append(other)
                    Q=canon(Q+((l,b),));assert Q is not None
                B.pay('demand_excluded_dimension',len(Q)-len(Hleft))
                todo.extend(reversed(children))
        memo[key]=out
        if out is None:remember_empty(mask,H)
        return out
    ans=ask(root,H)
    return (None if ans is None else chart(n,canon(ans))[0]),width

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

def test_exact_one_demand():
    rng=Random(3692026);checks=0
    for n in range(9):
        for _ in range(90):
            F=tuple(tuple((rng.randrange(1<<n),rng.randrange(2)) for j in range(rng.randrange(7))) for i in range(rng.randrange(8)))
            S=span(a for G in F for a,b in G)
            H=tuple((lift(0,S,rng.randrange(1<<len(S))),rng.randrange(2)) for _ in range(rng.randrange(5)))
            valid=lambda x:all(sum(b^((a&x).bit_count()%2) for a,b in G)==1 for G in F) and all((a&x).bit_count()%2==b for a,b in H)
            truth=any(valid(x) for x in range(1<<n));x,w=join_exact_one_demand(n,F,Budget(1000000),H)
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
            z,w=join_exact_one_demand(len(V),F,Budget(1000000));x=None if z is None else lift(u,V,z)
        assert (x is not None)==truth and (x is None or valid(x));checks+=1
    try:join_exact_one_demand(1,(((1,0),),),Budget(0));assert False
    except Exhausted:pass
    for n in (8,16,32,64):
        u,V=chart(n,canon((((1<<n)-1,1),)))
        F=tuple((value(V,1<<j),u>>j&1) for j in range(n))
        x,w=join_exact_one_demand(len(V),(F,F,F),Budget(10000000))
        assert lift(u,V,x).bit_count()==1 and w==n-1
    print('exact_one_demand',checks,'controls PASS')

def test_onehot_exclusion_core():
    rng=Random(2611369);checks=cores=0
    for n in range(9):
        for _ in range(100):
            G=tuple((rng.randrange(1<<n),rng.randrange(2)) for i in range(rng.randrange(9)))
            H=canon((rng.randrange(1<<n),rng.randrange(2)) for i in range(rng.randrange(n+1)))
            if H is None:continue
            E=onehot_exclusion_core(n,G,H,Budget(10000000))
            valid=lambda x:sum(b^((a&x).bit_count()%2) for a,b in G)==1
            truth=any(valid(x) and satisfies(x,H,()) for x in range(1<<n))
            assert (E is None)==truth;checks+=1
            if E is not None:
                assert canon(H+E)==H and len(E)<=len(G).bit_length()
                assert not any(valid(x) and satisfies(x,E,()) for x in range(1<<n))
                cores+=1
    for d in range(1,8):
        n=(1<<d)-1;G=tuple((1<<i,0) for i in range(n))
        H=canon((sum(((j>>i)&1)<<(j-1) for j in range(1,n+1)),0) for i in range(d))
        assert len(onehot_exclusion_core(n,G,H,Budget(100000000)))==d
    for n in (8,16,32,64,128):
        u,V=chart(n,canon((((1<<n)-1,1),)))
        G=tuple((value(V,1<<j),u>>j&1) for j in range(n))
        x=chart(len(V),canon((a,b^int(j<3)) for j,(a,b) in enumerate(G)))[0]
        H=canon(rows(tuple(1<<i for i in range(len(V))),x))
        E=onehot_exclusion_core(len(V),G,H,Budget(100000000))
        assert E is not None and canon(H+E)==H and len(E)==2
        assert all(canon(E+tuple((a,b^int(i==j)) for i,(a,b) in enumerate(G))) is None for j in range(n))
    print('onehot_exclusion_core',checks,cores,'controls PASS')

def test_cached_empty_cover():
    rng=Random(2611369);checks=collective=proved=0
    for n in range(9):
        for _ in range(140):
            H=canon((rng.randrange(1<<n),rng.randrange(2)) for j in range(rng.randrange(n+1)))
            if H is None:continue
            F=tuple(G for _ in range(rng.randrange(9)) if (G:=canon((rng.randrange(1<<n),rng.randrange(2)) for j in range(rng.randrange(n+1)))) is not None)
            T=[x for x in range(1<<n) if satisfies(x,H,())]
            want=all(any(satisfies(x,E,()) for E in F) for x in T)
            B=Budget(10000000);got=cached_empty_cover(n,H,F,B,8)
            assert not got or want
            checks+=1;proved+=got
            collective+=got and not any(canon(H+E)==H for E in F)
    for n in (3,8,16,32,64,128):
        H=canon(((2,0),(4,0)));F=[canon(((1,0),(2,0))),canon(((1,1),(4,0)))]
        assert not any(canon(H+E)==H for E in F)
        B=Budget(1000000);assert cached_empty_cover(n,H,F,B,2)
        assert not cached_empty_cover(n,H,F,B,1)
        a=rng.randrange(1<<n)
        shift=lambda E:canon((s,b^((s&a).bit_count()%2)) for s,b in E)
        assert cached_empty_cover(n,shift(H),[shift(E) for E in F],B,2)
    H=canon(((4,0),(8,0),(16,0),(32,0)))
    F=[canon(((1,q&1),(2,q>>1),(1<<(q+2),0))) for q in range(4)]
    assert cached_empty_cover(6,H,F,Budget(10000),4)
    assert not cached_empty_cover(6,H,F,Budget(10000),3)
    try:cached_empty_cover(6,H,F,Budget(0),4);assert False
    except Exhausted:pass
    print('cached_empty_cover',checks,proved,collective,'controls PASS')


def main():
    test_cached_empty_cover()
    test_onehot_exclusion_core()
    test_exact_one_demand()
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
