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


def exclude(F,shifts,p,B,pairs=True,max_pivots=4096):
    """Return a replayable constant contradiction, or None (inconclusive)."""
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
            if s==0:return tuple(proof+[(j,t,tuple(ops),c)])
            if len(basis)>=max_pivots:return None
            basis[s]=(len(proof),A);proof.append((j,t,tuple(ops),c))
    return None


def verify(F,proof,p,pairs=True,B=None):
    """Replay source combinations; never trust producer pivot decisions."""
    if p not in PRIMES or not proof:return False
    G=tuple(generators(F,p,pairs,B));rows=[]
    for j,t,ops,c in proof:
        if not (0<=j<len(G) and t>=0 and 0<c<p):return False
        if B is not None:B.pay('character_verify_source',1+len(G[j]))
        A={s^t:w for s,w in G[j].items()}
        for k,w in ops:
            if not (0<=k<len(rows) and 0<=w<p):return False
            if B is not None:B.pay('character_verify_reduce',1+len(rows[k]))
            add(A,rows[k],w,p)
        if B is not None:B.pay('character_verify_row',1+len(A))
        rows.append({s:w*c%p for s,w in A.items()})
    return rows[-1]=={0:1}


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


def main():
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
