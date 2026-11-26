"""X3C sharp-weight parity fibre: polynomial one-hot pair hull descent."""
from itertools import combinations, product
from random import Random
from check_pnp_affine_normal_components import (bits, canon, chart, lift,
    restrict, simplify, satisfies, Budget, Exhausted)
from check_pnp_normal_boundary_join import span, orth, value, join
from check_pnp_adaptive_signed_escape import add, point
from check_pnp_signed_quotient_minimum import minimum


def incidence(m,sets):
    assert m%3==0 and all(len(set(S))==3 and all(0<=i<m for i in S) for S in sets)
    return tuple(sum(1<<j for j,S in enumerate(sets) if i in S) for i in range(m))


def cover(R,x):return all((a&x).bit_count()==1 for a in R)


def local_hull(u,V,A,C,B):
    """All locally feasible one-hot pairs; compute exact affine hull of image."""
    U=A|C;J=tuple(1<<i for i in bits(U));d=len(J)
    B.pay('project',1+(len(V)+1)*d)
    p=value(J,u);W=span(value(J,v) for v in V);N=orth(d,W)
    target=value(N,p);a=value(J,A);c=value(J,C);common=a&c
    sig=[value(N,1<<i) for i in range(d)];S=[]
    for i in bits(common):
        B.pay('shared_choice')
        if sig[i]==target:S.append(1<<i)
    # Separate choices: match syndrome signatures, not all binary labels.
    D={}
    for j in bits(c&~a):
        B.pay('choice_index');D.setdefault(sig[j],[]).append(j)
    L={}
    for i in bits(a&~c):
        B.pay('choice_index');L.setdefault(sig[i],[]).append(i)
    for t,I in L.items():
        B.pay('choice_lookup');K=D.get(target^t,())
        if not K:continue
        # Each compatible signature class is a complete bipartite graph.
        # Two stars span its entire affine edge image, without a Cartesian join.
        for i in I:
            B.pay('star_edge');S.append((1<<i)|(1<<K[0]))
        for j in K[1:]:
            B.pay('star_edge');S.append((1<<I[0])|(1<<j))
    if not S:return None
    B.pay('hull',1+len(S)*d)
    p=S[0];K=span(s^p for s in S)
    return tuple((lift(0,J,b),(b&p).bit_count()%2) for b in orth(d,K))


def mod_image(A,b,n,e,B):
    """Exact mod-2 image of the integer solution fibre modulo 2**e."""
    q=1<<e;T=[[a%q for a in row]+[c%q] for row,c in zip(A,b)]
    P=[];active=set(range(n));B.pay('mod_input',1+len(T)*(n+1))
    while q>1 and T:
        B.pay('mod_scan',len(T)*(n+1))
        pivot=next(((i,j) for i,row in enumerate(T) for j in sorted(active) if row[j]&1),None)
        if pivot is None:
            if any(row[-1]&1 for row in T):return None
            T=[[a//2 for a in row] for row in T];q//=2;B.pay('mod_divide',len(T)*(n+1));continue
        i,j=pivot;row=T.pop(i);inv=pow(row[j],-1,q);row=[a*inv%q for a in row]
        P.append((sum((row[k]&1)<<k for k in active),row[-1]&1))
        active.remove(j);B.pay('mod_pivot',1+(len(T)+1)*(n+1))
        T=[[(a-v[j]*c)%q for a,c in zip(v,row)] for v in T]
    return canon(P)


def modular_rows(n,R,e,B):
    return mod_image([[(a>>j)&1 for j in range(n)] for a in R],[1]*len(R),n,e,B)


def close(n,R,B,pairs=True,required=()):
    """Every original cover remains in the returned affine carrier."""
    P=canon(tuple((a,1) for a in R)+tuple(required))
    while P is not None:
        B.pay('closure_round',1+n+len(R));u,V=chart(n,P)
        if cover(R,u):return P,u
        H=[]
        for A in sorted(set(R)):
            q=local_hull(u,V,A,A,B)
            if q is None:return None,None
            H.extend(q)
        if pairs:
            for A,C in combinations(sorted(set(R)),2):
                B.pay('row_pair');q=local_hull(u,V,A,C,B)
                if q is None:return None,None
                H.extend(q)
        Q=canon(P+tuple(H))
        if Q is None:return None,None
        if Q==P:return P,None
        assert len(Q)>len(P);B.pay('rank_drop',len(Q)-len(P));P=Q
    return None,None


def affine_onehot_close(n,row_bits,B,required=(),pairs=True):
    """Transport existing one-hot pair hull to a demanded affine row family.

    Returns (sound retained demand, original attaining point), or (None,None)
    for certified emptiness. A nonempty retained demand without a point is
    inconclusive; no original solution is lost. Share identical affine bits
    across rows, preserving within-row multiplicity.
    """
    H=canon(required)
    if H is None:return None,None
    u,V=chart(n,H);S=[];offset=0;R=[];index={}
    for G in row_bits:
        copies={};row=0
        for a,b in G:
            k=copies.get((a,b),0);copies[a,b]=k+1;key=(a,b,k)
            if key not in index:
                index[key]=len(S);offset|=b<<len(S);S.append(a)
            row|=1<<index[key]
        R.append(row)
    m=len(S);B.pay('affine_hull_image',1+m*(1+len(V)))
    o=offset^value(S,u);W=span(value(S,v) for v in V)
    N=orth(m,W);P=tuple((a,(a&o).bit_count()%2) for a in N)
    Q,w=close(m,tuple(R),B,pairs=pairs,required=P)
    if Q is None:return None,None
    B.pay('affine_hull_reopen',1+m*(1+len(Q)))
    H1=canon(H+tuple((lift(0,S,a),b^((a&offset).bit_count()%2)) for a,b in Q))
    assert H1 is not None
    if w is None:return H1,None
    K=canon(H1+tuple((a,((w^offset)>>j)&1) for j,a in enumerate(S)))
    assert K is not None;x=chart(n,K)[0]
    assert all(sum(b^((a&x).bit_count()%2) for a,b in G)==1 for G in row_bits)
    return H1,x

def weight_chart(n,u,V,B):
    M={}
    for i in range(n):
        B.pay('weight_term',1+len(V))
        a=value(V,1<<i);b=1^((u>>i)&1);add(M,canon(((a,b),)),1)
    return M


def row_capacity(n,R,B):
    """A row hitting set bounds the number of pairwise disjoint selected columns."""
    U=(1<<n)-1;J=[]
    while U:
        B.pay('capacity_scan',1+len(R));i=max(range(len(R)),key=lambda i:(R[i]&U).bit_count())
        if not R[i]&U:raise AssertionError('uncovered source column')
        U&=~R[i];J.append(i)
    return tuple(J)


def solve(m,sets,cap,width=4):
    R=incidence(m,sets);n=len(sets);B=Budget(cap)
    try:
        B.pay('input',1+m+3*n)
        if len(row_capacity(n,R,B))<m//3:return None,B.stats,True
        D=modular_rows(n,R,max(1,m.bit_length()),B)
        if D is None:return None,B.stats,True
        P,x=close(n,R,B,required=D)
        if P is None or x is not None:return x,B.stats,True
        u,V=chart(n,P);k=m//3;M=weight_chart(n,u,V,B)
        # Sharp weight is attained exactly by a cover. A relaxed lower bound
        # strictly above k excludes it; an exact min at k gives safe descent.
        a,exact=minimum(M,len(V),B,width)
        if a>k:return None,B.stats,True
        if exact:
            assert a==k
            for i in range(n):
                B.pay('weight_pin');Q=canon(P+((1<<i,0),))
                if Q is None:continue
                v,W=chart(n,Q);z,ok=minimum(weight_chart(n,v,W,B),len(W),B,width)
                if z>k:P=canon(P+((1<<i,1),))
                elif ok:P=Q
                else:break
            else:
                x=chart(n,P)[0]
                if cover(R,x):return x,B.stats,True
        # Existing exact forbidden-flat consumer; no new search architecture.
        F=tuple(((1<<j,1),(1<<i,1)) for a in R for i,j in combinations(bits(a),2))
        B.pay('pair_flats',len(F));q=restrict(n,P,F,B)
        if q is None:return None,B.stats,True
        u,V,H=q;H=simplify(H,B)
        if () in H:return None,B.stats,True
        y,_=join(len(V),H,B)
        if y is None:return None,B.stats,True
        x=lift(u,V,y);assert x.bit_count()==k and cover(R,x)
        return x,B.stats,True
    except (Exhausted,RecursionError):return None,B.stats,False


def test_affine_onehot_close():
    rng=Random(26113692026);checks=0
    for n in range(9):
        for _ in range(160):
            F=tuple(tuple((rng.randrange(1<<n),rng.randrange(2)) for i in range(rng.randrange(7))) for j in range(rng.randrange(8)))
            H=canon((rng.randrange(1<<n),rng.randrange(2)) for i in range(rng.randrange(n+1)))
            if H is None:continue
            valid=lambda x:all(sum(b^((a&x).bit_count()%2) for a,b in G)==1 for G in F)
            truth=[x for x in range(1<<n) if satisfies(x,H,()) and valid(x)]
            P,w=affine_onehot_close(n,F,Budget(20000000),H)
            if P is None:assert not truth
            else:
                assert canon(P+H)==P and all(satisfies(x,P,()) for x in truth)
                if w is not None:assert w in truth
            checks+=1
    # Every row pair is feasible, but the collective closure excludes all.
    F=(((15,0),(26,0),(28,1)),((29,1),(18,0)),((31,1),(13,1),(15,0),(25,0),(8,1),(13,1)),((16,0),(15,1)),((29,1),(4,1)),((7,1),(26,1),(6,1),(10,1)))
    valid=lambda x,G:sum(b^((a&x).bit_count()%2) for a,b in G)==1
    assert all(any(valid(x,G) and valid(x,J) for x in range(32)) for G,J in combinations(F,2))
    assert affine_onehot_close(5,F,Budget(20000000))==(None,None)
    print('affine_onehot_close',checks,'collective control PASS')

def main():
    test_affine_onehot_close()
    rng=Random(369);tests=checks=verified=empty=unknown=modchecks=modgain=0
    for m in (3,6,9,12):
        for _ in range(100):
            n=rng.randrange(1,11);sets=[tuple(sorted(rng.sample(range(m),3))) for j in range(n)]
            R=incidence(m,sets);S=[x for x in range(1<<n) if cover(R,x)]
            P=canon((a,1) for a in R)
            if P is not None:
                u,V=chart(n,P);M=weight_chart(n,u,V,Budget(100000))
                for y in range(1<<len(V)):
                    x=lift(u,V,y);assert point(M,y)==x.bit_count()>=m//3
                    assert (x.bit_count()==m//3)==cover(R,x);checks+=1
                for A,C in combinations(sorted(set(R)),2):
                    B=Budget(1000000);H=local_hull(u,V,A,C,B)
                    T=[x for y in range(1<<len(V)) if ((x:=lift(u,V,y))&A).bit_count()==1 and (x&C).bit_count()==1]
                    if not T:assert H is None
                    else:
                        J=A|C;t=T[0]&J;K=span((x&J)^t for x in T)
                        assert H is not None and len(H)==J.bit_count()-len(K)
                        assert all(satisfies(x,H,()) for x in T)
                    tests+=1
            D=modular_rows(n,R,max(1,m.bit_length()),Budget(1000000))
            assert D is not None or not S
            if D is not None:
                assert all(satisfies(t,D,()) for t in S)
                assert P is not None and len(D)>=len(P)
                modgain+=len(D)>len(P)
            B=Budget(1000000);Q,x=close(n,R,B);assert (Q is not None or not S) and (x is None or x in S)
            if Q is not None:assert all(satisfies(t,Q,()) for t in S)
            x,_,done=solve(m,sets,1000000)
            if x is not None:assert done and x in S;verified+=1
            elif done:assert not S;empty+=1
            else:unknown+=1
    # High rank pair: two disjoint one-hot scopes, all parity-consistent.
    for d in (16,32,64,128):
        n=2*d;A=(1<<d)-1;C=A<<d;P=canon(((A,1),(C,1)));u,V=chart(n,P);B=Budget(1000000)
        H=local_hull(u,V,A,C,B);assert H==P and B.stats['star_edge']==2*d-1
        print('high_rank_pair',n,'parity_dimension',len(V),'joint_labels',d*d,'star_edges',B.stats['star_edge'],'charged',sum(B.stats.values()))
    # Exact modular projection, independently enumerate lifted residues in tests only.
    for n in range(5):
        for _ in range(40):
            e=rng.randrange(1,4);q=1<<e;m=rng.randrange(5)
            A=[[rng.randrange(q) for j in range(n)] for i in range(m)];b=[rng.randrange(q) for i in range(m)]
            want={sum((v&1)<<i for i,v in enumerate(x)) for x in product(range(q),repeat=n) if all(sum(a*v for a,v in zip(row,x))%q==c for row,c in zip(A,b))}
            D=mod_image(A,b,n,e,Budget(1000000));got=set() if D is None else {x for x in range(1<<n) if satisfies(x,D,())}
            assert got==want;modchecks+=1
    # Pair descent makes a strict rank gain on a genuine original X3C source.
    S=[(2,5,8),(2,3,6),(3,4,8),(1,2,8),(3,5,7),(3,6,7),(3,4,7),(5,7,8),(1,4,7),(4,6,7),(0,2,5),(0,2,5),(3,4,8),(0,4,6),(0,5,8),(0,1,6)]
    R=incidence(9,S);U,z=close(16,R,Budget(1000000),False);P,x=close(16,R,Budget(1000000))
    assert z is None and len(U)==9 and len(P)==14 and cover(R,x)
    print('pair_gain','rank',len(U),len(P),'witness',x)
    # Cyclic Latin exact cover: parity and pair hull stall, higher 2-adic obstruction.
    for q in (4,8):
        S=[(i,q+j,2*q+(i+j)%q) for i in range(q) for j in range(q)];R=incidence(3*q,S);n=q*q
        P,x=close(n,R,Budget(10000000));assert P is not None and x is None
        e=q.bit_length()-1;B=Budget(1000000);D=modular_rows(n,R,e-1,B);assert D is not None
        assert modular_rows(n,R,e,B) is None
        y,C,done=solve(3*q,S,1000000);assert done and y is None
        print('latin',q,'parity_pair_rank',len(P),'first_reject_depth',e,'charged',sum(C.values()))
    # Space barrier survives every modular depth and even the pair-hull closure.
    S=[T for T in combinations(range(12),3) if min(T)<3];R=incidence(12,S);n=len(S)
    pos=((0,3,4),(1,5,6),(2,7,8),(2,9,10),(0,1,11));neg=(0,1,2)
    assert all(sum(i in T for T in pos)-int(i in neg)==1 for i in range(12))
    assert all(T in S for T in pos+(neg,))
    B=Budget(10000000);D=modular_rows(n,R,5,B);P,x=close(n,R,B,required=D)
    assert D is not None and P is not None and x is None and len(P)==13
    J=row_capacity(n,R,B);assert len(J)==3
    y,C,done=solve(12,S,1000000);assert done and y is None and C['capacity_scan']>0
    print('space_barrier',n,'pair_rank',len(P),'capacity',len(J),'charged',sum(C.values()))
    # Modular feasibility is not exact cover: nonnegative/integer bounds still matter.
    A=[[2,0],[0,1]];assert mod_image(A,[2,0],2,3,Budget(1000))==((2,0),(1,1))
    assert solve(6,[(0,1,2)],0)[2] is False
    print(dict(fixtures=400,pair_hulls=tests,weight_comparisons=checks,verified=verified,empty=empty,unknown=unknown,mod_projection=modchecks,mod_rank_gain=modgain))

if __name__=='__main__':main()
