"""Collective preference conflicts and witness-only signed quotient descent."""
from random import Random
from check_pnp_affine_normal_components import (canon, chart, lift, restrict,
    simplify, satisfies, Budget, Exhausted, cnf_flats)
from check_pnp_collective_fibre_escape import coordinates, domain, dot, blocks, size
from check_pnp_adaptive_signed_escape import (add, intersect, forest, masked,
    marginal, point, reopen, adaptive)
from check_p0_signed_conflict_20261126 import conflict, conditioned as transform


def collective_core(n,terms,remaining,B):
    # Reuse the donor's inconsistent-activation / single-entailment detector.
    B.pay('conflict_scan',1+sum(len(A)+1 for A,w in terms))
    p=conflict(terms,remaining)
    if p:return tuple(i for i in range(len(terms)) if p>>i&1)
    I=tuple(i for i,(A,w) in enumerate(terms) if w<0 and remaining[i])
    P=canon(row for i in I for row in terms[i][0]);assert P is not None
    u,V=chart(n,P);groups={}
    for j,(A,w) in enumerate(terms):
        if w<=0 or not remaining[j]:continue
        B.pay('collective_cell',len(A)+1)
        D=canon((sum(dot(a,v)<<i for i,v in enumerate(V)),b^dot(a,u)) for a,b in A)
        if D is None:continue
        key=tuple(a for a,b in D);labels=groups.setdefault(key,{})
        labels.setdefault(tuple(b for a,b in D),j)
        if len(labels)==1<<len(key):return tuple(sorted(I+tuple(labels.values())))
    return ()


def pack(n,c,terms,B,early=True):
    remaining=[abs(w) for A,w in terms];z=c+sum(min(0,w) for A,w in terms);receipt=[]
    while not early or z<=0:
        I=collective_core(n,terms,remaining,B)
        if not I:break
        q=min(remaining[i] for i in I);assert q>0
        B.pay('conflict_charge',len(I));receipt.append((I,q));z+=q
        for i in I:remaining[i]-=q
    return z,receipt


def replay(n,c,terms,receipt,B):
    rem=[abs(w) for A,w in terms];z=c+sum(min(0,w) for A,w in terms)
    for I,q in receipt:
        assert I and len(I)==len(set(I)) and q>0 and all(0<=i<len(rem) and rem[i]>=q for i in I)
        assert collective_core(n,terms,[int(i in I) for i in range(len(rem))],B)
        for i in I:rem[i]-=q
        z+=q
    return z


def conflict_floor(M,n,H,B):
    B.pay('conflict_input',1+len(M)+sum(len(A)+1 for A in H))
    c,T=transform(M.get((),0),[(A,w) for A,w in sorted(M.items()) if A and w],H)
    return pack(n,c,T,B)[0]


def gated(M,H,B,width):
    """Exact admissible mask, or a signed negative penalty if width cap fails."""
    Q=dict(M)
    for A in H:
        P=dict(Q);intersect(Q,A,-1,B,P)
        if len(P)>width:
            K=1+sum(abs(w) for w in M.values());Q=dict(M)
            for C in H:B.pay('penalty');add(Q,C,-K)
            return Q
        Q=P
    return Q


def mass(n,Q,P,B):
    B.pay('signed_mass',1+len(Q));return sum(w*size(A,n,P) for A,w in Q.items())


def positive_point(n,M,H,B,width=256):
    Q=gated(M,H,B,width)
    # Root, actual chart domains, and both sides of actual normal hyperplanes.
    P0={A for A in Q if A};P0.update(H)
    normals={a for A in P0 for a,b in A}
    P0.update(((a,b),) for a in normals for b in (0,1))
    for P in [()]+sorted(P0,key=lambda A:(len(A),A)):
        B.pay('probe');c=mass(n,Q,P,B)
        if c<=0:continue
        B.pay('positive_probe');R=P
        # Pin the free coordinates of the original affine restriction.
        piv={a.bit_length()-1 for a,b in P}
        for i in range(n):
            if i in piv:continue
            A=canon(R+((1<<i,0),));assert A is not None
            q=mass(n,Q,A,B)
            if q>0:R=A;c=q
            else:R=canon(R+((1<<i,1),));assert R is not None;c-=q
            assert c>0
        y=chart(n,R)[0]
        assert satisfies(y,(),H) and point(M,y)==c and c>0
        return y,c,P
    return None


def block_witness(n,F,V,B,width=256,promotions=4):
    U=coordinates(n,V);d=len(U);k=len(V);H=set();E=[]
    B.pay('block_chart',n+1)
    for G in F:
        B.pay('block_scan',1+len(G));A=canon((sum(dot(a,v)<<i for i,v in enumerate(U+list(V))),b) for a,b in G)
        if A is None:continue
        P=domain(A,d)
        if len(A)==len(P):H.add(P)
        else:E.append(A)
    H=tuple(sorted(H));T=forest(E,n,B);R=set(range(len(E)));Q={():1}
    order=sorted(R,key=lambda i:(len(E[i]),-sum(i in (a,b) for a,b,_ in T),i))
    for stage in range(min(promotions,len(E))+1):
        B.pay('checkpoint');L=masked(Q,E,R,T,B);M=marginal(L,d,k,B)
        q=positive_point(d,M,H,B,width)
        if q is not None:
            y,c,P=q;x=reopen((tuple(U),tuple(V),tuple(E),L,c,stage),y,B)
            assert satisfies(x,(),F);return x,stage,P,c
        if stage==min(promotions,len(E)):break
        i=order[stage];A=dict(Q);intersect(Q,E[i],-1,B,A)
        if len(A)>width:break
        Q=A;R.remove(i);B.pay('promoted')
    return None


def solve(n,required,F,cap):
    B=Budget(cap)
    try:
        B.pay('input',n+len(required)+sum(len(G)+1 for G in F)+1)
        q=restrict(n,required,F,B)
        if q is None:return None,B.stats,True
        u,V,H=q;H=simplify(H,B);d=len(V)
        if () in H:return None,B.stats,True
        if not H:return u,B.stats,True
        # Allocate independent caps to source-derived blocks, smaller blocks first.
        W=list(blocks(d,H,B));W.sort(key=lambda A:(len(A),A));share=B.left//len(W)
        for A in W:
            local=Budget(share)
            try:q=block_witness(d,H,A,local)
            except Exhausted:q=None
            B.pay('block_work',min(share,share-local.left))
            if q is not None:
                x=lift(u,V,q[0]);assert satisfies(x,required,F);return x,B.stats,True
        return None,B.stats,False
    except (Exhausted,RecursionError):return None,B.stats,False


def main():
    rng=Random(369);floors=receipts=probes=positive=fixtures=verified=empty=unknown=fallback=0
    for n in range(7):
        for _ in range(40):
            M={():rng.randrange(-6,7)}
            for i in range(rng.randrange(9)):
                A=canon((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,n+2)))
                add(M,A,rng.randrange(-6,7))
            H=tuple(A for _ in range(rng.randrange(4)) if (A:=canon((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,n+2)))) is not None)
            c,T=transform(M.get((),0),[(A,w) for A,w in sorted(M.items()) if A and w],H)
            B=Budget(1000000);z,R=pack(n,c,T,B,False);assert replay(n,c,T,R,B)==z
            vals=[point(M,x) for x in range(1<<n) if satisfies(x,(),H)]
            assert not vals or z<=min(vals);floors+=1;receipts+=len(R)
            for width in (1,256):
                q=positive_point(n,M,H,B,width);probes+=1
                if q is not None:
                    y,v,P=q;assert satisfies(y,(),H) and point(M,y)==v>0;positive+=1
            P=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            F=tuple(A for _ in range(rng.randrange(9)) if (A:=canon((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,n+2)))) is not None)
            S=[x for x in range(1<<n) if satisfies(x,P,F)]
            x,_,done=solve(n,P,F,1000000);fixtures+=1
            if x is not None:assert done and x in S;verified+=1
            elif done:assert not S;empty+=1
            else:
                unknown+=1
                y,_,complete=adaptive(n,P,F,1000000,admissible_envelope=conflict_floor)
                assert complete and (y is not None)==bool(S)
                if y is not None:assert y in S
                fallback+=1
    # Donor blind spot: four rank-two positive orientations cover all points.
    for n in (2,16,64,128):
        M={canon(((1,a),(2,b))):1 for a in (0,1) for b in (0,1)}
        B=Budget(10000);assert conflict_floor(M,n,(),B)==1
    # Conditional cover only on preferred negative domain; shared cost charged once.
    M={():2,((4,0),):-2};M.update({canon(((4,0),(1,a),(2,b))):1 for a in (0,1) for b in (0,1)})
    assert conflict_floor(M,3,(),Budget(10000))==1
    # One admissible fibre is fully covered, another is free; global escape fails.
    F=tuple(canon(G) for G in (((1,0),(2,0)),((1,0),(2,1))))
    B=Budget(10000);q=block_witness(2,F,(2,),B, promotions=0)
    assert q is not None and q[1]==0 and satisfies(q[0],(),F)
    # Negative root integral, positive conditional fibre at y=1; no promotions.
    for k in (8,16,32,64):
        V=tuple(1<<i for i in range(1,k+1));F=tuple(canon(((1,0),(v,0))) for v in V)
        B=Budget(1000000);q=block_witness(k+1,F,V,B,promotions=0)
        assert q is not None and q[1]==0 and q[2]==((1,1),) and q[3]==1<<k
        assert satisfies(q[0],(),F)
        print('negative_root',k,'conditional_mass',q[3],'charged',sum(B.stats.values()))
    # Actual conflict callback admission on a nonpositive independent floor.
    from check_pnp_adaptive_signed_escape import certificate
    F=tuple(canon(G) for G in (((1,0),(2,0)),((1,1),(4,0))))
    assert certificate(3,F,(2,4),Budget(10000)) is None
    B=Budget(10000);q=certificate(3,F,(2,4),B,admissible_envelope=conflict_floor)
    assert q is not None and q[1][-2:]==(2,0) and B.stats['conflict_scan']>0
    for y in (0,1):assert satisfies(reopen(q[1],y,B),(),F)
    # Even a positive singleton need not have a positive offered affine probe.
    M={():1};M.update({((1<<i,0),):-1 for i in range(4)})
    assert point(M,15)==1 and positive_point(4,M,(),Budget(10000)) is None
    # Force the negative-penalty fallback rather than an exact hard mask.
    M={():2,((1,0),):-3};H=(((1,0),),)
    assert positive_point(1,M,H,Budget(1000),width=1)[:2]==(1,2)
    assert solve(3,(),(),0)[2] is False
    print(dict(floors=floors,receipts=receipts,probes=probes,positive=positive,fixtures=fixtures,verified=verified,empty=empty,unknown=unknown,fallback=fallback,controls='PASS'))

if __name__=='__main__':main()
