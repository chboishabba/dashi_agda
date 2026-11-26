"""Odd-field signed character-ideal exclusion on original exact-one rows.
Classical polynomial calculus in the binary character group algebra.
Finite caps are optional proof discovery limits, not completeness claims.
"""
from itertools import combinations
from check_pnp_affine_normal_components import Budget, canon, chart, lift
from check_pnp_normal_boundary_join import value

PRIMES=(3,5,7,11,101)


def add(A,B,c,p):
    for s,w in B.items():
        v=(A.get(s,0)+c*w)%p
        if v:A[s]=v
        elif s in A:del A[s]


def generators(F,p,pairs=True,B=None):
    """2(sum bits-1), and 4 times each within-row bit product."""
    assert p in PRIMES
    for G in F:
        if B is not None:B.pay('character_source',1+len(G)+(len(G)*(len(G)-1)//2 if pairs else 0))
        A={};add(A,{0:len(G)-2},1,p)
        for s,b in G:add(A,{s:-(-1)**b},1,p)
        yield A
        if pairs:
            for (s,b),(t,c) in combinations(G,2):
                A={}
                for u,w in ((0,1),(s,-(-1)**b),(t,-(-1)**c),(s^t,(-1)**(b+c))):add(A,{u:w},1,p)
                yield A


def eliminate(F,shifts,p,B,pairs=True,max_pivots=4096):
    """Return the source proof rows and whether constant one was derived."""
    assert p in PRIMES and max_pivots>=0
    G=tuple(generators(F,p,pairs,B));basis={};proof=[]
    for t in shifts:
        for j,g in enumerate(G):
            B.pay('character_generator',1+len(g));A={s^t:w for s,w in g.items()};ops=[]
            while A:
                s=max(A);w=A[s]
                if s not in basis:break
                k,C=basis[s];B.pay('character_reduce',1+len(C));add(A,C,-w,p);ops.append((k,-w%p))
            if not A:continue
            s=max(A);c=pow(A[s],-1,p);A={u:w*c%p for u,w in A.items()}
            B.pay('character_pivot',1+len(A)+len(ops))
            if s==0:return tuple(proof+[(j,t,tuple(ops),c)]),True
            if len(basis)>=max_pivots:return tuple(proof),False
            basis[s]=(len(proof),A);proof.append((j,t,tuple(ops),c))
    return tuple(proof),False


def exclude(F,shifts,p,B,pairs=True,max_pivots=4096):
    """Return a replayable constant contradiction, or None (inconclusive)."""
    proof,empty=eliminate(F,shifts,p,B,pairs,max_pivots)
    return proof if empty else None


def replay(F,proof,p,pairs=True,B=None):
    """Replay source combinations; never trust producer pivot decisions."""
    if p not in PRIMES or proof is None:return None
    G=tuple(generators(F,p,pairs,B));rows=[]
    for j,t,ops,c in proof:
        if not (0<=j<len(G) and t>=0 and 0<c<p):return None
        if B is not None:B.pay('character_verify_source',1+len(G[j]))
        A={s^t:w for s,w in G[j].items()}
        for k,w in ops:
            if not (0<=k<len(rows) and 0<=w<p):return None
            if B is not None:B.pay('character_verify_reduce',1+len(rows[k]))
            add(A,rows[k],w,p)
        if B is not None:B.pay('character_verify_row',1+len(A))
        rows.append({s:w*c%p for s,w in A.items()})
    return rows


def verify(F,proof,p,pairs=True,B=None):
    rows=replay(F,proof,p,pairs,B)
    return bool(rows) and rows[-1]=={0:1}


def source_shifts(F,degree=1,B=None):
    if degree not in (0,1,2):raise ValueError("degree must be 0, 1 or 2")
    S=sorted({s for G in F for s,b in G if s});T={0}
    if B is not None:B.pay("character_shift_build",1+sum(map(len,F))+len(S)+(len(S)*(len(S)-1)//2 if degree==2 else 0))
    if degree>=1:T.update(S)
    if degree>=2:T.update(s^t for s,t in combinations(S,2))
    return sorted(T,key=lambda t:(t!=0,t))


def compact(proof,B=None):
    """Retain only the transitive dependencies of the final contradiction."""
    active={len(proof)-1};todo=list(active)
    while todo:
        i=todo.pop();ops=proof[i][2]
        if B is not None:B.pay('character_proof_slice',1+len(ops))
        for k,w in ops:
            if k not in active:active.add(k);todo.append(k)
    ids={i:j for j,i in enumerate(sorted(active))}
    return tuple((j,t,tuple((ids[k],w) for k,w in ops),c)
                 for i in sorted(active) for j,t,ops,c in (proof[i],))


def transport_proof(proof,V,a,p,B=None):
    """Pull the exact certificate along z=a XOR V y, with stable generator IDs."""
    if p not in PRIMES:raise ValueError("unsupported odd prime")
    out=[]
    for j,t,ops,c in proof:
        if B is not None:B.pay('character_transport',1+len(V)+len(ops))
        sign=(-1)**((t&a).bit_count()%2)
        out.append((j,value(V,t),tuple((k,w*sign%p) for k,w in ops),c*sign%p))
    return tuple(out)


def demand_exclusion(n,F,H,B,degree=1,p=3,max_pivots=4096):
    """Verify exclusion on the exact demanded affine fibre; False is UNKNOWN."""
    B.pay("character_demand",1+len(H))
    P=canon(H)
    if P is None:return True
    u,V=chart(n,P);B.pay('character_pullback',1+sum(len(G) for G in F)*(1+len(V)))
    R=tuple(tuple((value(V,s),b^((s&u).bit_count()%2)) for s,b in G) for G in F)
    S=source_shifts(R,degree,B);B.pay('character_shifts',len(S))
    proof=exclude(R,S,p,B,max_pivots=max_pivots)
    if proof is None:return False
    if not verify(R,compact(proof,B),p,B=B):raise AssertionError('invalid character contradiction')
    return True


def quotient_normal(A,basis,p,B):
    """Reduce every pivot column, including those below free columns."""
    A=dict(A);R={}
    while A:
        s=max(A);w=A[s]
        if s in basis:
            C=basis[s];B.pay('character_normal',1+len(C));add(A,C,-w,p)
        else:
            B.pay('character_free');R[s]=A.pop(s)
    return R


def replay_span(F,proof,p,B,pairs=True):
    """Rebuild a span from replayed source combinations; rechart can merge pivots."""
    R=replay(F,proof,p,pairs,B)
    if R is None:return None
    basis={}
    for A in R:
        C=dict(A)
        while C and max(C) in basis:
            s=max(C);D=basis[s];B.pay('character_replay_pivot',1+len(D));add(C,D,-C[s],p)
        if C:
            s=max(C);c=pow(C[s],-1,p);basis[s]={t:w*c%p for t,w in C.items()}
    return basis


def character_relation_span(F,shifts,queries,p,B,max_pivots=4096):
    """Retain a replayed proof span and explicit proportionality certificates."""
    proof,empty=eliminate(F,shifts,p,B,max_pivots=max_pivots)
    if empty:proof=compact(proof,B) # preserve compact contradiction replay
    basis=replay_span(F,proof,p,B)
    if basis is None:raise AssertionError('invalid character proof')
    if empty:
        assert not quotient_normal({0:1},basis,p,B)
        return proof,(),0,basis
    groups={};relations=[]
    for s in sorted(set(queries)|{0}):
        B.pay('character_query');A=quotient_normal({s:1},basis,p,B)
        if not A:return proof,(),s,basis
        c=A[min(A)];inv=pow(c,-1,p)
        B.pay('character_projective_key',1+len(A))
        key=tuple(sorted((t,w*inv%p) for t,w in A.items()))
        if key in groups:
            t,d=groups[key];ratio=c*pow(d,-1,p)%p
            relations.append((s,t,ratio))
            if ratio not in (1,p-1):break
        else:groups[key]=(s,c)
    return proof,tuple(relations),None,basis


def character_relations(F,shifts,queries,p,B,max_pivots=4096):
    proof,relations,zero,_=character_relation_span(F,shifts,queries,p,B,max_pivots)
    return proof,relations,zero


def span_accepts_relations(basis,relations,zero,p,B):
    if zero is not None:
        return not relations and zero>=0 and not quotient_normal({zero:1},basis,p,B)
    for s,t,c in relations:
        if min(s,t)<0 or not 0<c<p:return False
        A={s:1};add(A,{t:1},-c,p)
        if quotient_normal(A,basis,p,B):return False
    return True


def verify_relations(F,proof,relations,zero,p,B):
    """Replay from original generators; verify the claimed proportionalities."""
    basis=replay_span(F,proof,p,B)
    return basis is not None and span_accepts_relations(basis,relations,zero,p,B)


def relation_pins(relations,zero,p):
    if zero is not None or any(c not in (1,p-1) for s,t,c in relations):return None
    return canon((s^t,int(c!=1)) for s,t,c in relations)


def transport_relations(relations,zero,V,a,p):
    return (tuple((value(V,s),value(V,t),c*(-1)**(((s^t)&a).bit_count()%2)%p)
                  for s,t,c in relations),None if zero is None else value(V,zero))


def character_consequences(F,shifts,probes,p,B,max_pivots=4096):
    """Verified affine consequences; None is a certified contradiction."""
    proof,relations,zero,basis=character_relation_span(F,shifts,probes,p,B,max_pivots)
    if not span_accepts_relations(basis,relations,zero,p,B):raise AssertionError('invalid character consequence')
    return relation_pins(relations,zero,p)


def quotient_reopen(n,F,basis,p,B,cap=64):
    """Attempt an original witness using a capped finite character module.

    Full ideal closure makes its multiplication maps commuting involutions.
    Partial spans need not have that property: check the eigensection and
    independently verify the original row assignment. Failure is UNKNOWN.
    """
    if cap<1 or 0 in basis:return None
    S=tuple(s for s,b in canon((s,0) for G in F for s,b in G))
    Q=[0];seen={0};M={};i=0
    while i<len(Q):
        t=Q[i];i+=1
        for s in S:
            B.pay('character_module_edge');A=quotient_normal({s^t:1},basis,p,B)
            M[s,t]=A
            for a in A:
                if a not in seen:
                    if len(Q)>=cap:return None
                    Q.append(a);seen.add(a)
    B.pay('character_module_dimension',len(Q))
    def act(s,v):
        out={}
        for t,w in v.items():
            A=M[s,t];B.pay('character_module_act',1+len(A));add(out,A,w,p)
        return out
    def eigen(s,v,b):
        A=act(s,v);add(A,v,-(-1)**b,p);return not A
    v={0:1};pins=[]
    for s in S:
        w=act(s,v);u=dict(v);add(u,w,1,p);b=0
        if not u:
            b=1;u=dict(v);add(u,w,-1,p)
        if not u or not eigen(s,u,b):return None
        pins.append((s,b));v=u
    if not all(eigen(s,v,b) for s,b in pins):return None
    P=canon(pins);assert P is not None
    x=chart(n,P)[0]
    B.pay('character_module_verify',1+sum(map(len,F)))
    if not all(sum(b^((s&x).bit_count()%2) for s,b in G)==1 for G in F):return None
    return x


def restrict_character_span(basis,V,a,p,B):
    """Linear image of the replayed consequence span under an affine embedding."""
    out={};freq={}
    for C in basis.values():
        A={}
        for s,w in C.items():
            if s not in freq:
                B.pay('character_restrict_map',1+len(V))
                freq[s]=(value(V,s),(-1)**((s&a).bit_count()%2))
            t,c=freq[s];B.pay('character_restrict_term');add(A,{t:w},c,p)
        while A and max(A) in out:
            s=max(A);D=out[s];B.pay('character_restrict_reduce',1+len(D));add(A,D,-A[s],p)
        if A:
            s=max(A);c=pow(A[s],-1,p);out[s]={t:w*c%p for t,w in A.items()}
            B.pay('character_restrict_pivot',1+len(A))
            if s==0:return out
    return out


def restriction_reopen(n,F,basis,p,B,steps):
    """One-path original-row restriction, sharing the replayed proof span.

    Empty projected spans are not feasibility evidence. A constant in the
    projected span excludes that child; failure of greedy discovery is UNKNOWN.
    Returns only an independently verified witness, or None.
    """
    assert steps>=0
    original=F;origin=0;V0=tuple(1<<i for i in range(n))
    if 0 in basis:return None
    for step in range(min(steps,n)+1):
        B.pay('character_path_verify',1+sum(map(len,F)))
        bad=[G for G in F if sum(b for s,b in G)!=1]
        if not bad:
            assert all(sum(b^((s&origin).bit_count()%2) for s,b in G)==1 for G in original)
            return origin
        if step==min(steps,n):return None
        G=min(bad,key=len);candidates=[];best=None
        for j in range(len(G)):
            B.pay('character_path_branch',1+len(G))
            H=canon((s,b^int(i==j)) for i,(s,b) in enumerate(G))
            if H is None:continue
            a,V=chart(len(V0),H);assert len(V)<len(V0)
            B.pay('character_path_score',1+sum(map(len,F)))
            # Check original row residual at the branch origin before mapping.
            score=sum(abs(sum(b^((s&a).bit_count()%2) for s,b in J)-1) for J in F)
            if not score:
                x=lift(origin,V0,a)
                assert all(sum(b^((s&x).bit_count()%2) for s,b in J)==1 for J in original)
                return x
            candidates.append(((score,len(V),j),a,V))
        for key,a,V in sorted(candidates):
            Q=restrict_character_span(basis,V,a,p,B)
            if 0 in Q:
                B.pay('character_path_excluded');continue
            B.pay('character_path_image',1+sum(map(len,F))*(1+len(V)))
            R=tuple(tuple((value(V,s),b^((s&a).bit_count()%2)) for s,b in J) for J in F)
            best=(key,a,V,R,Q);break
        if best is None:return None
        _,a,V,F,basis=best
        origin=lift(origin,V0,a);V0=tuple(lift(0,V0,v) for v in V)
        B.pay('character_path_step')
    return None


def demand_character_close(n,F,H,B,degree=1,p=3,max_pivots=4096,quotient_cap=0,path_steps=0):
    """Sound original affine refinement and optional original witness.

    Share one replayed elimination span across both consumers. None carrier
    certifies empty; a carrier without witness is not a feasibility decision.
    """
    B.pay('character_demand',1+len(H));P=canon(H)
    if P is None:return None,None
    u,V=chart(n,P);B.pay('character_pullback',1+sum(len(G) for G in F)*(1+len(V)))
    R=tuple(tuple((value(V,s),b^((s&u).bit_count()%2)) for s,b in G) for G in F)
    reps={0:0}
    for G in F:
        for s,b in G:reps.setdefault(value(V,s),s)
    freq=tuple(reps);eq=tuple(value(freq,1<<j) for j in range(len(V)))
    proof,rel,zero,basis=character_relation_span(R,source_shifts(R,degree,B),freq,p,B,max_pivots)
    if not span_accepts_relations(basis,rel,zero,p,B):raise AssertionError('invalid character consequence')
    Q=relation_pins(rel,zero,p)
    if Q is None:return None,None
    pins=[]
    for s,b in Q:
        B.pay('character_reopen',1+len(freq)*max(1,len(V)))
        C=canon((v,(s>>j)&1) for j,v in enumerate(eq));assert C is not None
        a=lift(0,[reps[t] for t in freq],chart(len(freq),C)[0])
        pins.append((a,b^((a&u).bit_count()%2)))
    C=canon(P+tuple(pins));assert C is not None
    if not quotient_cap and not path_steps:return C,None
    x=chart(n,C)[0]
    B.pay('character_pin_verify',1+sum(map(len,F)))
    if all(sum(b^((s&x).bit_count()%2) for s,b in G)==1 for G in F):return C,x
    z=None
    if path_steps:
        a,W=chart(len(V),Q)
        B.pay('character_path_pins',1+sum(map(len,R))*(1+len(W)))
        J=tuple(tuple((value(W,s),b^((s&a).bit_count()%2)) for s,b in G) for G in R)
        K=restrict_character_span(basis,W,a,p,B) if Q else basis
        if 0 in K:return None,None
        y=restriction_reopen(len(W),J,K,p,B,path_steps)
        if y is not None:z=lift(a,W,y)
    if z is None and quotient_cap:z=quotient_reopen(len(V),R,basis,p,B,quotient_cap)
    if z is not None:
        x=lift(u,V,z)
        assert all((s&x).bit_count()%2==b for s,b in C)
        assert all(sum(b^((s&x).bit_count()%2) for s,b in G)==1 for G in F)
        return C,x
    return C,None


def demand_refinement(n,F,H,B,degree=1,p=3,max_pivots=4096):
    return demand_character_close(n,F,H,B,degree,p,max_pivots)[0]


def test_character_consequences():
    from random import Random
    from check_pnp_affine_normal_components import satisfies, Exhausted
    def valid(F,x):return all(sum(b^((s&x).bit_count()%2) for s,b in G)==1 for G in F)
    # Two different normals forced equal without either individual normal fixed.
    F=(((1,0),(2,1)),)
    P=character_consequences(F,(0,),range(4),3,Budget(10000))
    assert P==((3,0),),P
    assert demand_refinement(2,F,(),Budget(10000),degree=0)==((3,0),)
    # Full character image recovers exactly every affine equation true on solutions.
    rng=Random(36927);full=bounded=empty=rank=transport=0
    for n in range(6):
     for _ in range(60):
      F=tuple(tuple((rng.randrange(1<<n),rng.randrange(2)) for j in range(rng.randrange(6))) for i in range(rng.randrange(6)))
      T=[x for x in range(1<<n) if valid(F,x)]
      for p in (3,5,7):
       P=character_consequences(F,range(1<<n),range(1<<n),p,Budget(5000000))
       assert (P is None)==(not T)
       if T:
        Q=canon((s,(s&T[0]).bit_count()%2) for s in range(1<<n) if len({(s&x).bit_count()%2 for x in T})==1)
        assert P==Q,(F,P,Q);rank+=len(P)
       else:empty+=1
       full+=1
      H=canon((rng.randrange(1<<n),rng.randrange(2)) for i in range(rng.randrange(n+1)))
      if H is None:continue
      T=[x for x in T if satisfies(x,H,())]
      P=demand_refinement(n,F,H,Budget(5000000),degree=1)
      assert (P is not None or not T) and (P is None or all(satisfies(x,P,()) for x in T))
      assert P is None or canon(P+H)==P
      bounded+=1
      a=rng.randrange(1<<n);shift=lambda G:tuple((s,b^((s&a).bit_count()%2)) for s,b in G)
      Q=demand_refinement(n,tuple(shift(G) for G in F),shift(H),Budget(5000000),degree=1)
      assert (Q is None or all(satisfies(x^a,Q,()) for x in T)) and (Q is not None or not T)
      transport+=1
    try:demand_refinement(2,(((1,0),(2,1)),),(),Budget(0));assert False
    except Exhausted:pass
    # Full pair-hull closure is inconclusive on this inhabited affine source.
    F=(((47,1),(29,1),(74,0),(21,0)),((68,0),(107,1),(84,0)),((33,0),(48,1),(99,0)))
    from check_pnp_normal_boundary_join import orth,span
    P=();T=list(range(128))
    while True:
        rows=[]
        for A,C in combinations(F,2):
            S=[z for z in T if valid((A,C),z)];assert S
            rows.extend((s,(s&S[0]).bit_count()%2) for s in orth(7,span(z^S[0] for z in S)))
        Q=canon(P+tuple(rows));assert Q is not None
        if Q==P:break
        P=Q;T=[z for z in T if satisfies(z,P,())]
    assert len(P)==3 and not valid(F,chart(7,P)[0])
    Q=demand_refinement(7,F,P,Budget(1000000));assert len(Q)==5
    assert [z for z in range(128) if valid(F,z)]==[57,89,109]
    assert all(satisfies(z,Q,()) for z in (57,89,109)) and valid(F,chart(7,Q)[0])
    # A truncated elimination is still safe; an absent relation is not exclusion.
    for cap in (0,1,2,4):
        Q=demand_refinement(7,F,P,Budget(1000000),max_pivots=cap)
        assert Q is not None and all(satisfies(z,Q,()) for z in (57,89,109))
    assert not verify(F,None,3)
    print('character_consequences',dict(full=full,empty=empty,rank=rank,bounded=bounded,transport=transport), 'pair_hull_rank_3_to_5 PASS')


def test_constructive_character_quotient():
    from random import Random
    from check_pnp_affine_normal_components import Exhausted
    rng=Random(369261127);full=bounded=transported=0
    for n in range(7):
        for _ in range(60):
            F=tuple(tuple((rng.randrange(1<<n),rng.randrange(2)) for i in range(rng.randrange(7))) for j in range(rng.randrange(7)))
            valid=lambda x:all(sum(b^((s&x).bit_count()%2) for s,b in G)==1 for G in F)
            truth=[x for x in range(1<<n) if valid(x)]
            for p in (3,5,7):
                B=Budget(10000000)
                proof,rel,zero=character_relations(F,range(1<<n),range(1<<n),p,B)
                assert verify_relations(F,proof,rel,zero,p,B) and (relation_pins(rel,zero,p) is not None)==bool(truth)
                basis=replay_span(F,proof,p,B);x=quotient_reopen(n,F,basis,p,B,1<<n)
                assert (x is not None)==bool(truth) and (x is None or valid(x))
                if truth:
                    P=relation_pins(rel,zero,p)
                    assert P==canon((s,(s&truth[0]).bit_count()%2) for s in range(1<<n) if all((s&(x^truth[0])).bit_count()%2==0 for x in truth))
                    if rel:
                        s,t,c=rel[0];assert not verify_relations(F,proof,((s,t,-c%p),),None,p,B)
                a=rng.randrange(1<<n);V=tuple(rng.randrange(1<<n) for i in range(rng.randrange(n+1)))
                R=tuple(tuple((value(V,s),b^((s&a).bit_count()%2)) for s,b in G) for G in F)
                r,z=transport_relations(rel,zero,V,a,p)
                assert verify_relations(R,transport_proof(proof,V,a,p,B),r,z,p,B)
                full+=1;transported+=1
            H=canon((rng.randrange(1<<n),rng.randrange(2)) for i in range(rng.randrange(n+1)))
            if H is None:continue
            T=[x for x in truth if all((s&x).bit_count()%2==b for s,b in H)]
            for degree in (0,1):
                P,w=demand_character_close(n,F,H,Budget(10000000),degree=degree,max_pivots=32,quotient_cap=8)
                if P is None:assert not T and w is None
                else:
                    assert canon(P+H)==P and all(all((s&x).bit_count()%2==b for s,b in P) for x in T)
                    assert w is None or w in T
                bounded+=1
    S=[(6,9,17),(2,9,13),(2,14,16),(0,5,15),(3,6,13),(1,13,15),(10,13,17),(0,4,8),(6,12,17),(3,8,12),(0,5,16),(4,7,9),(7,11,14),(10,12,17),(0,5,17),(1,3,4),(5,9,16),(6,10,16),(7,10,11),(1,2,13),(1,7,12),(4,7,15),(8,11,14),(1,8,14),(3,4,15),(5,10,11),(2,11,15),(2,9,12),(6,8,14),(0,3,16)]
    R=tuple(sum(1<<j for j,s in enumerate(S) if i in s) for i in range(18))
    u,V=chart(30,canon((r,1) for r in R))
    F=tuple(tuple((value(V,1<<j),u>>j&1) for j in range(30) if r>>j&1) for r in R)
    B=Budget(10000000);P,w=demand_character_close(len(V),F,(),B,quotient_cap=64)
    assert len(P)==9 and w is not None and all((lift(u,V,w)&r).bit_count()==1 for r in R)
    assert B.stats['character_module_dimension']==4
    Q,w0=demand_character_close(len(V),F,(),Budget(10000000),quotient_cap=1)
    assert Q==P and w0 is None
    # A non-sign proportionality is itself an exact contradiction over F5.
    A=(((4,0),(6,1),(3,1),(1,0)),)
    proof,rel,zero=character_relations(A,(0,),range(8),5,Budget(1000000))
    assert zero is None and any(c not in (1,4) for s,t,c in rel)
    assert verify_relations(A,proof,rel,zero,5,Budget(1000000)) and relation_pins(rel,zero,5) is None
    try:demand_character_close(len(V),F,(),Budget(0),quotient_cap=64);assert False
    except Exhausted:pass
    print(dict(constructive_full=full,constructive_bounded=bounded,constructive_transport=transported,module_control='PASS'))


def test_character_restriction_path():
    from random import Random
    from check_pnp_affine_normal_components import Exhausted
    rng=Random(261136928);full=partial=transport=0
    for n in range(7):
        for _ in range(100):
            F=tuple(tuple((rng.randrange(1<<n),rng.randrange(2)) for i in range(rng.randrange(7))) for j in range(rng.randrange(7)))
            valid=lambda x:all(sum(b^((s&x).bit_count()%2) for s,b in G)==1 for G in F)
            T=[x for x in range(1<<n) if valid(x)]
            for p in (3,5,7):
                B=Budget(10000000);proof,_=eliminate(F,range(1<<n),p,B);basis=replay_span(F,proof,p,B)
                x=restriction_reopen(n,F,basis,p,B,n)
                assert (x is not None)==bool(T) and (x is None or x in T);full+=1
                if T:
                    a=rng.randrange(1<<n);V=tuple(1<<i for i in range(n) if rng.randrange(2))
                    Q=restrict_character_span(basis,V,a,p,B)
                    assert (0 in Q)==(not any(valid(lift(a,V,y)) for y in range(1<<len(V))))
                    if 0 not in Q:
                        R=tuple(tuple((value(V,s),b^((s&a).bit_count()%2)) for s,b in G) for G in F)
                        pp,_=eliminate(R,range(1<<len(V)),p,B);K=replay_span(R,pp,p,B)
                        assert len(K)==len(Q) and all(not quotient_normal(A,K,p,B) for A in Q.values())
                    transport+=1
                proof,_=eliminate(F,(0,),p,B,max_pivots=8);basis=replay_span(F,proof,p,B)
                x=restriction_reopen(n,F,basis,p,B,n)
                assert x is None or x in T;partial+=1
    for r in (4,8,16,32,64):
        n=2*r+1;F=tuple(((1,0),(1<<(2*i+1),0),(1<<(2*i+2),0)) for i in range(r))
        B=Budget(10000000);proof,_=eliminate(F,(0,),3,B);basis=replay_span(F,proof,3,B)
        assert quotient_reopen(n,F,basis,3,B,8) is None
        assert restriction_reopen(n,F,basis,3,B,n)==1
        assert restriction_reopen(n,F,basis,3,B,0) is None
    try:restriction_reopen(1,(((1,0),),),{},3,Budget(0),1);assert False
    except Exhausted:pass
    print(dict(restriction_full=full,restriction_partial=partial,restriction_transport=transport,star_controls='PASS'))


def main():
    test_character_restriction_path()
    test_constructive_character_quotient()
    test_character_consequences()
    from random import Random
    from check_pnp_affine_normal_components import Exhausted
    rng=Random(3692611);full=bounded=exclusions=translated=transported=0
    for n in range(6):
        for _ in range(60):
            F=tuple(tuple((rng.randrange(1<<n),rng.randrange(2)) for j in range(rng.randrange(7))) for i in range(rng.randrange(7)))
            H=canon((rng.randrange(1<<n),rng.randrange(2)) for i in range(rng.randrange(n+1)))
            if H is None:continue
            u,V=chart(n,H)
            R=tuple(tuple((value(V,s),b^((s&u).bit_count()%2)) for s,b in G) for G in F)
            valid=lambda x:all(sum(b^((s&x).bit_count()%2) for s,b in G)==1 for G in F)
            truth=any(valid(lift(u,V,z)) for z in range(1<<len(V)))
            for p in (3,5,7):
                B=Budget(3000000);Q=exclude(R,range(1<<len(V)),p,B)
                assert (Q is None)==truth;full+=1
                if Q is not None:
                    Q=compact(Q,B);assert verify(R,Q,p,B=B);exclusions+=1
                    a0=rng.randrange(1<<len(V));W=tuple(1<<i for i in range(len(V)) if rng.randrange(2))
                    R0=tuple(tuple((value(W,s),b^((s&a0).bit_count()%2)) for s,b in G) for G in R)
                    assert verify(R0,transport_proof(Q,W,a0,p,B),p,B=B);transported+=1
            got=demand_exclusion(n,F,H,Budget(3000000));assert not got or not truth;bounded+=1
            a=rng.randrange(1<<n)
            shift=lambda G:tuple((s,b^((s&a).bit_count()%2)) for s,b in G)
            assert demand_exclusion(n,tuple(shift(G) for G in F),shift(H),Budget(3000000))==got
            translated+=1
    # Actual original empty source surviving parity-capacity and pair-hull closure.
    S=[(5,13,17),(5,14,16),(3,10,17),(0,2,16),(3,4,16),(1,10,12),(0,7,15),(6,7,10),(1,12,13),(4,5,13),(1,3,12),(0,4,6),(8,10,17),(3,7,9),(1,14,15),(9,12,15),(2,13,16),(2,12,17),(2,5,15),(6,7,8),(6,7,14),(8,11,17),(4,11,15),(5,8,11),(2,3,9),(6,9,13),(9,10,11),(0,1,16),(0,4,14),(8,11,14)]
    R=tuple(sum(1<<j for j,s in enumerate(S) if i in s) for i in range(18));u,V=chart(30,canon((r,1) for r in R))
    F=tuple(tuple((value(V,1<<j),u>>j&1) for j in range(30) if r>>j&1) for r in R)
    assert not any(all((lift(u,V,z)&r).bit_count()==1 for r in R) for z in range(1<<len(V)))
    assert exclude(F,(0,),3,Budget(3000000)) is None
    assert exclude(F,source_shifts(F),3,Budget(3000000),pairs=False) is None
    B=Budget(3000000);Q=exclude(F,source_shifts(F),3,B);assert Q is not None
    generated=len(Q);Q=compact(Q,B);assert verify(F,Q,3,B=B)
    j,t,ops,c=Q[-1];bad=Q[:-1]+((j,t,ops,c%2+1),)
    assert not verify(F,bad,3)
    assert demand_exclusion(len(V),F,(),Budget(3000000))
    try:demand_exclusion(len(V),F,(),Budget(0));assert False
    except Exhausted:pass
    print('original_30',len(V),len(source_shifts(F)),generated,len(Q),sum(B.stats.values()))
    print(dict(full=full,exclusions=exclusions,bounded=bounded,translated=translated,transported=transported,controls='PASS'))


if __name__=='__main__':main()
