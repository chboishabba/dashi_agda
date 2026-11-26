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


def character_consequences(F,shifts,probes,p,B,max_pivots=4096):
    """Sound affine equations from projectively equal character normal forms.

    Each reduced form differs from its original character by a replayed
    source combination. None means contradiction, not failure to refine.
    With a capped row space, the resulting affine hull may be too large.
    """
    proof,empty=eliminate(F,shifts,p,B,max_pivots=max_pivots)
    if empty:
        if not verify(F,compact(proof,B),p,B=B):raise AssertionError('invalid character contradiction')
        return None
    # Reconstruct every used row independently of the producer's pivots.
    R=replay(F,proof,p,B=B)
    if R is None:raise AssertionError('invalid character proof')
    basis={}
    for A in R:
        s=max(A);assert A[s]==1 and s not in basis;basis[s]=A
    order=sorted(basis,reverse=True);groups={};pins=[]
    for s in sorted(set(probes)|{0}):
        A={s:1};B.pay('character_normal_scan',1+len(order))
        for t in order:
            if t in A:
                B.pay('character_normal_reduce',1+len(basis[t]));add(A,basis[t],-A[t],p)
        if not A:return None # A character cannot vanish at any original point.
        c=A[min(A)];inv=pow(c,-1,p)
        B.pay('character_projective_key',1+len(A))
        key=tuple(sorted((t,w*inv%p) for t,w in A.items()))
        if key in groups:
            t,b=groups[key];ratio=c*pow(b,-1,p)%p
            if ratio not in (1,p-1):return None # characters take only +/-1
            pins.append((s^t,int(ratio!=1)))
        else:groups[key]=(s,c)
    B.pay('character_pin_canon',1+len(pins))
    return canon(pins)


def demand_refinement(n,F,H,B,degree=1,p=3,max_pivots=4096):
    """Lift all discovered relations back into the original row-normal span."""
    B.pay('character_demand',1+len(H));P=canon(H)
    if P is None:return None
    u,V=chart(n,P);B.pay('character_pullback',1+sum(len(G) for G in F)*(1+len(V)))
    R=tuple(tuple((value(V,s),b^((s&u).bit_count()%2)) for s,b in G) for G in F)
    # Representative for every projected source character, plus zero.
    reps={0:0}
    for G in F:
        for s,b in G:reps.setdefault(value(V,s),s)
    # Keep every relation in the original span, including combinations created
    # by Gaussian canonicalization of projective equalities.
    freq=tuple(reps);equations=tuple((value(freq,1<<j),1<<j) for j in range(len(V)))
    # Solve each lifted normal as a linear combination of source frequencies.
    Q=character_consequences(R,source_shifts(R,degree,B),freq,p,B,max_pivots)
    if Q is None:return None
    pins=[]
    for s,b in Q:
        B.pay('character_reopen',1+len(freq)*max(1,len(V)))
        C=canon((v,(s&j).bit_count()%2) for v,j in equations);assert C is not None
        a=lift(0,[reps[t] for t in freq],chart(len(freq),C)[0])
        pins.append((a,b^((a&u).bit_count()%2)))
    return canon(P+tuple(pins))


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


def main():
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
