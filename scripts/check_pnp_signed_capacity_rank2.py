"""Bounded complete rank-two signed-envelope discovery for a fixed portfolio.
No claim of arbitrary-rank discovery or complete SAT. Charges precede work.
"""
from itertools import combinations, product
from check_pnp_affine_normal_components import canon, bits, chart, satisfies
from check_pnp_signed_capacity_square import add, row_ledger
from check_pnp_signed_capacity_cube import restrict_ledger


def lower(M,parity):
    v=M.get(0,0)-sum(abs(c) for a,c in M.items() if a)
    w=(v+1)//2
    return w+((parity-w)%2)


def portfolio(M,caps,B,pairs=True):
    out=[]
    for i,(m,c) in enumerate(zip(M,caps)):
        B.pay('rank2_row',1+len(m));out.append((m,c,1,(i,)))
    if pairs:
        for i,j in combinations(range(len(M)),2):
            B.pay('rank2_row_pair',1+len(M[i])+len(M[j]));Q=dict(M[i])
            for a,c in M[j].items():add(Q,a,c)
            out.append((Q,caps[i]+caps[j],0,(i,j)))
    return out


def directions(P,B):
    D=set()
    for M,cap,parity,source in P:
        A=sorted(set(M)|{0});B.pay('rank2_differences',1+len(A)**2)
        D.update(a^b for a,b in combinations(A,2))
    return sorted(D)


def planes(D,B):
    seen=set()
    for a,b in combinations(D,2):
        B.pay('rank2_plane_candidate');W=tuple(sorted((a,b,a^b)))
        if W not in seen:
            seen.add(W);yield W[:2]


def inspect(P,W,B):
    allowed=[];excluded=[]
    for v in product((0,1),repeat=len(W)):
        H=tuple(zip(W,v))
        for M,cap,p,source in P:
            B.pay('rank2_fold',1+(1+len(W))*len(M))
            l=lower(restrict_ledger(M,H),p)
            if l>cap:
                excluded.append((v,source,l,cap));break
        else:allowed.append(v)
    return allowed,excluded


def forced(W,allowed):
    if not allowed:return None
    out=[]
    for mask in range(1,1<<len(W)):
        vals={sum(v[i] for i in bits(mask))%2 for v in allowed}
        if len(vals)==1:
            a=0
            for i in bits(mask):a^=W[i]
            out.append((a,vals.pop()))
    return canon(out)


def observe(P,B,rank=2):
    """Return (forced equations or None for empty, receipts, scanned planes).
    Complete for affine consequences of each tested section's allowed labels,
    not arbitrary combinations of the retained nonlinear forbidden sections.
    """
    assert rank in (1,2)
    for M,cap,p,src in P:
        B.pay('rank2_base',1+len(M))
        if lower(M,p)>cap:return None,[((),[((),src,lower(M,p),cap)])],0
    D=directions(P,B);pins=[];receipts=[];count=0
    for W in [(a,) for a in D]:
        allowed,excluded=inspect(P,W,B);Q=forced(W,allowed)
        if excluded:receipts.append((W,excluded))
        if Q is None:return None,receipts,count
        pins.extend(Q)
    B.pay('rank2_join',1+(1+len(pins))**2);K=canon(pins)
    if K is None or K or rank==1:return K,receipts,count
    for W in planes(D,B):
        count+=1;allowed,excluded=inspect(P,W,B);Q=forced(W,allowed)
        if excluded:receipts.append((W,excluded))
        if Q is None:return None,receipts,count
        pins.extend(Q)
    B.pay('rank2_join',1+(1+len(pins))**2)
    return canon(pins),receipts,count


def screen(n,R,H,caps,B):
    """Original-coordinate strict rank closure; a stalled carrier is UNKNOWN."""
    B.pay('rank2_scope',1+(n+1)*(1+len(H)+len(R)))
    assert H==canon(H) and canon(H+tuple((r,1) for r in R))==H
    assert len(R)==len(caps)
    while True:
        d=n-len(H);B.pay('rank2_chart',1+n+(1+d)*(1+len(H)))
        u,V=chart(n,H);B.pay('rank2_origin',1+n+sum(r.bit_count() for r in R))
        if all((r&u).bit_count()<=c for r,c in zip(R,caps)):
            assert satisfies(u,H,());return H,u,'origin'
        B.pay('rank2_group',1+sum(r.bit_count() for r in R)*(1+d))
        M=[row_ledger(r,u,V) for r in R]
        Q,_,_=observe(portfolio(M,caps,B),B)
        if Q is None:return None,None,'rank2_empty'
        if not Q:return H,None,'stalled'
        free=tuple(j for j in range(n) if j not in {a.bit_length()-1 for a,b in H})
        P=tuple((sum(1<<free[j] for j in bits(a)),b) for a,b in Q)
        B.pay('rank2_source_join',1+(1+len(H)+len(P))**2);K=canon(H+P)
        if K is None:return None,None,'rank2_conflict'
        assert len(K)>len(H);H=K
