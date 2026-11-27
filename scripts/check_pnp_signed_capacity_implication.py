"""Cross-plane affine unit propagation over certified signed capacity exclusions.

No independent-Boolean assumption: all literals live on one GF(2) carrier.
None = proved empty; () = no forced equations, not a satisfiability claim.
"""
from check_pnp_affine_normal_components import canon, bits, chart, restrict, simplify, satisfies
from check_pnp_signed_capacity_square import row_ledger
from check_pnp_signed_capacity_cube import restrict_ledger
from check_pnp_signed_capacity_rank2 import lower, portfolio, observe


def verify_receipts(P, receipts, B):
    """Recompute every exclusion against its named ledger on the SAME chart."""
    by_source={src:(M,cap,p) for M,cap,p,src in P}
    F=set()
    for W, excluded in receipts:
        B.pay('imp_receipt_basis',1+len(W)**2)
        assert len(W)<=2 and len(canon(tuple((a,0) for a in W)))==len(W)
        for v,src,l,cap in excluded:
            assert len(v)==len(W) and all(b in (0,1) for b in v)
            M,c,p=by_source[src];B.pay('imp_receipt_verify',1+(1+len(W))*len(M))
            H=canon(tuple(zip(W,v)))
            assert H is not None and c==cap and lower(restrict_ledger(M,H),p)==l and l>c
            F.add(H)
    return tuple(sorted(F))


def reduce_flat(G,H,B):
    """Reduce a forbidden conjunction in ambient slots, retaining signs."""
    B.pay('imp_reduce',1+(1+len(G))*(1+len(H)))
    out=[]
    for a,b in G:
        for r,s in H:
            if a & (1<<(r.bit_length()-1)):a^=r;b^=s
        out.append((a,b))
    return canon(out)


def propagate(F,H,P,B,proof=None):
    """Deterministic affine unit closure; a conflict refutes the assumption.
    Each successful batch adds at least one independent equation.
    The final envelope is evaluated on the FULL implied normal subspace.
    """
    B.pay('imp_initial_join',1+len(H)**2)
    H=canon(H)
    while H is not None:
        pins=[]
        for G in F:
            K=reduce_flat(G,H,B)
            if K is None:continue  # forbidden orientation unreachable
            if not K:
                if proof is not None:proof.append(('flat_conflict',H,G))
                return None,'flat_conflict'
            if len(K)==1:
                a,b=K[0];pins.append((a,b^1))
                if proof is not None:proof.append(('unit',H,G,(a,b^1)))
        if not pins:break
        B.pay('imp_unit_join',1+(len(H)+len(pins))**2)
        K=canon(H+tuple(pins))
        if K is None:
            if proof is not None:proof.append(('parity_conflict',H,tuple(pins)))
            return None,'parity_conflict'
        assert len(K)>len(H);H=K
    if H is None:
        if proof is not None:proof.append(('initial_conflict',))
        return None,'parity_conflict'
    for M,c,p,src in P:
        B.pay('imp_conditioned_floor',1+(1+len(H))*len(M))
        l=lower(restrict_ledger(M,H),p)
        if l>c:
            if proof is not None:proof.append(('conditioned_floor',H,src,l,c,p))
            return None,'conditioned_floor'
    return H,'closed'


def deduce(F,P,B,base=(),audit=None):
    """Refute signed assumptions using propagation, not a branch search.
    Returns (forced equations or None, scoped refutation trace, simplified F).
    A surviving assumption is UNKNOWN, never certified feasible.
    """
    B.pay('imp_flat_input',1+sum(1+len(G) for G in F))
    F=simplify(tuple(sorted(set(F))),B)
    H,why=propagate(F,base,P,B,audit);trace=[]
    if H is None:return None,[((),why)],F
    D=set()
    for G in F:
        B.pay('imp_candidate',1+len(G))
        assert len(G)<=2
        D.update(a for a,b in G)
        if len(G)==2:D.add(G[0][0]^G[1][0])
    while True:
        pins=[]
        for a in sorted(D):
            K=reduce_flat(((a,0),),H,B)
            if K is None or not K:continue  # already fixed
            for b in (0,1):
                B.pay('imp_assumption')
                proof=[] if audit is not None else None
                Q,why=propagate(F,H+((a,b),),P,B,proof)
                if Q is None:
                    trace.append((H+((a,b),),why));pins.append((a,b^1))
                    if audit is not None:audit.append(('refuted_assumption',H,(a,b),why,proof))
        if not pins:return H,trace,F
        B.pay('imp_forced_join',1+(len(H)+len(pins))**2)
        K,why=propagate(F,H+tuple(pins),P,B,audit)
        if K is None:return None,trace+[(H+tuple(pins),why)],F
        assert len(K)>len(H);H=K


def screen(n,R,H,caps,B,audit=None,retained=None):
    """Preserve all paid nonlinear receipts in original free-slot coordinates.
    The enclosing partition consumer handles resource refusal transactionally.
    """
    B.pay('imp_scope',1+(n+1)*(1+len(H)+len(R)))
    assert H==canon(H) and canon(H+tuple((r,1) for r in R))==H
    assert len(R)==len(caps)
    original_F=set()
    while True:
        d=n-len(H);B.pay('imp_chart',1+n+(1+d)*(1+len(H)))
        u,V=chart(n,H)
        B.pay('imp_origin',1+n+sum(r.bit_count() for r in R))
        if all((r&u).bit_count()<=c for r,c in zip(R,caps)):
            assert satisfies(u,H,());return H,u,'origin'
        B.pay('imp_group',1+sum(r.bit_count() for r in R)*(1+d))
        M=[row_ledger(r,u,V) for r in R];P=portfolio(M,caps,B)
        Q,rec,_=observe(P,B)
        F=verify_receipts(P,rec,B)
        entry=None
        if audit is not None:
            entry=dict(scope=H,receipts=rec,verified=F,rank2_pins=Q,proof=[])
            audit.append(entry)
        if Q is None:return None,None,'rank2_empty'
        free=tuple(j for j in range(n) if j not in {a.bit_length()-1 for a,b in H})
        def reopen(G):
            return canon(tuple((sum(1<<free[j] for j in bits(a)),b) for a,b in G))
        B.pay('imp_original_receipts',1+sum(1+len(G)*max(1,d) for G in F))
        original_F.update(reopen(G) for G in F)
        B.pay('imp_receipt_pull',1+(1+n)*(1+len(H))*sum(1+len(G) for G in original_F))
        _,_,F=restrict(n,H,tuple(sorted(original_F)),B)
        if entry is not None:entry['retained_original_flats']=tuple(sorted(original_F));entry['pulled_flats']=F
        K,_,_=deduce(F,P,B,Q,None if entry is None else entry['proof'])
        if entry is not None:entry['derived']=K
        if K is None:return None,None,'imp_empty'
        if not K:
            if retained is not None:retained.extend(sorted(original_F))
            return H,None,'imp_stalled'
        B.pay('imp_source_join',1+(1+len(H)+len(K))**2)
        J=canon(H+reopen(K))
        if J is None:return None,None,'imp_conflict'
        assert len(J)>len(H);H=J
