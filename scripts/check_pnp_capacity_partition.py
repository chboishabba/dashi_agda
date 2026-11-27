"""Bounded disjoint row-capacity fibres in original coordinates.

Unlike an affine hull of a union, retain the nonlinear alternatives until a
witness, exact empty union, or budget refusal. Bounds are original point counts.
"""
from itertools import combinations
from math import comb
from check_pnp_affine_normal_components import bits,canon,chart,satisfies
from check_pnp_demand_strata import Allowance,ProbeLimit
from check_pnp_capacity_signed import Bound


def row_cells(n,H,r,c,B,fanout=128):
    """Exact disjoint allowed cells, or None on representation refusal."""
    u,V=chart(n,H);moving=0
    for v in V:moving|=v
    J=tuple(bits(r&moving));fixed=(r&u&~moving).bit_count()
    ks=tuple(k for k in range(min(len(J),c-fixed)+1) if (fixed+k)%2==1)
    count=sum(comb(len(J),k) for k in ks)
    if count>fanout:return None
    B.pay('row_partition_expand',1+count*(1+len(J))*(1+n+len(H)))
    out=[]
    for k in ks:
        for T in combinations(J,k):
            mask=sum(1<<j for j in T)
            P=canon(H+tuple((1<<j,int(bool(mask&(1<<j)))) for j in J))
            if P is not None:out.append(P)
    return tuple(out)


def partition(n,R,H,caps,B,nodes=32,fanout=128,closure=True,recovery=False,signed_screen=False,trace=None):
    """Witness-only or exact empty/unknown, with monotone candidate upper bound.

    Every live cell is disjoint in original coordinates; only verified empty
    cells are removed. A refused split leaves the entire parent in the frontier.
    """
    assert H==canon(H) and canon(H+tuple((r,1) for r in R))==H
    assert len(R)==len(caps)
    if any(c<1 for c in caps):return Bound(0,0)
    pending=[(H,tuple(range(len(R))))];upper=1<<(n-len(H));steps=0
    while pending and steps<nodes:
        P,I=pending[-1]
        try:
            B.pay('row_partition_node',1+n+len(P)+len(I));steps+=1
            if trace is not None:trace('enter',P,I,None)
            if signed_screen:
                if signed_screen=='implication':
                    from check_pnp_signed_capacity_implication import screen
                elif signed_screen=='rank2-components':
                    from check_pnp_signed_capacity_components import screen
                elif signed_screen=='rank2':
                    from check_pnp_signed_capacity_rank2 import screen
                elif signed_screen=='cube':
                    from check_pnp_signed_capacity_cube import screen
                else:
                    from check_pnp_signed_capacity_square import screen
                try:Q,y,reason=screen(n,R,P,caps,Allowance(B,B.left//4))
                except ProbeLimit:Q,y,reason=P,None,'refused'
                if trace is not None:trace('signed',Q,I,reason)
                if Q is None:
                    upper-=1<<(n-len(P));pending.pop();continue
                assert canon(P+Q)==Q
                upper+=(1<<(n-len(Q)))-(1<<(n-len(P)))
                P=Q;pending[-1]=(P,I)
                if y is not None:
                    assert satisfies(y,H,()) and all((r&y).bit_count()<=c for r,c in zip(R,caps))
                    return Bound(1,upper,y,steps)
            # Reuse original one-hot affine hull, not auxiliary duplicated columns.
            if closure and all(c==1 for c in caps):
                from check_pnp_exact_cover_pair_hull import close
                try:
                    Q,y=close(n,R,Allowance(B,B.left//4),pairs=False,required=P)
                except ProbeLimit:Q,y=P,None
                if trace is not None:trace('hull',Q,I,None)
                if Q is None:
                    upper-=1<<(n-len(P));pending.pop();continue
                assert canon(P+Q)==Q
                upper+=(1<<(n-len(Q)))-(1<<(n-len(P)))
                P=Q;pending[-1]=(P,I)
                if y is not None:
                    assert satisfies(y,H,()) and all((r&y).bit_count()<=c for r,c in zip(R,caps))
                    return Bound(1,upper,y,steps)
            u,V=chart(n,P);moving=0
            for v in V:moving|=v
            B.pay('row_partition_scan',1+len(V)+len(R)*(1+n))
            if all((r&u).bit_count()<=c for r,c in zip(R,caps)):
                return Bound(1,upper,u,steps)
            candidates=[]
            for i in I:
                r=R[i];c=caps[i];d=(r&moving).bit_count();fixed=(r&u&~moving).bit_count()
                if fixed+d<=c:continue
                kmax=min(d,c-fixed)
                size=sum(comb(d,k) for k in range(kmax+1) if (fixed+k)%2==1)
                candidates.append((size,-d,i))
            if not candidates:raise AssertionError('violated row lost from demand')
            _,_,i=min(candidates)
            if trace is not None:trace('split',P,I,i)
            cells=row_cells(n,P,R[i],caps[i],B,fanout)
            if cells is None:break
            J=tuple(j for j in I if j!=i)
            # Transaction: charge before changing frontier or mass.
            B.pay('row_partition_commit',1+len(cells)*(1+len(J)))
            upper+=sum(1<<(n-len(Q)) for Q in cells)-(1<<(n-len(P)))
            pending.pop();pending.extend((Q,J) for Q in reversed(cells))
        except ProbeLimit:break
    assert upper>=0
    if recovery and pending:
        return recover_frontier(n,R,H,caps,pending,upper,steps,B,signed_screen=signed_screen)
    return Bound(0,upper,None,steps)


def recover_cell(n,R,H,caps,B,signed_screen=False):
    """Reuse the normal-component, signed, and character owners on ONE cell.

    A completed component solve is decisive, but a cap refusal is not.
    No normal form is expanded without a precharged capacity representation.
    """
    from check_pnp_affine_normal_components import solve,Exhausted
    from check_pnp_capacity_geometry import violation_flats
    from check_pnp_capacity_signed import observe
    from check_pnp_capacity_character import discover_certificate,verify_certificate
    from check_pnp_capacity_contraction import contract
    volume=1<<(n-len(H));best=Bound(0,volume)
    if any(c<1 for c in caps):return Bound(0,0)
    if signed_screen:
        if signed_screen=='implication':
            from check_pnp_signed_capacity_implication import screen
        elif signed_screen=='rank2-components':
            from check_pnp_signed_capacity_components import screen
        elif signed_screen=='rank2':
            from check_pnp_signed_capacity_rank2 import screen
        elif signed_screen=='cube':
            from check_pnp_signed_capacity_cube import screen
        else:
            from check_pnp_signed_capacity_square import screen
        try:Q,y,reason=screen(n,R,H,caps,Allowance(B,B.left//4))
        except ProbeLimit:Q,y,reason=H,None,'refused'
        if Q is None:return Bound(0,0)
        assert canon(H+Q)==Q
        H=Q;volume=1<<(n-len(H));best=Bound(0,volume)
        if y is not None:return Bound(1,volume,y)
    def normal(A):
        F=violation_flats(n,R,H,caps,A)
        y=solve(n,H,F,A)
        return Bound(0,0) if y is None else Bound(1,volume,y)
    def signed(A):return observe(n,R,H,caps,A)[0]
    def character(A):
        c=discover_certificate(n,R,H,caps,Allowance(A,A.left//2),0)
        if c is not None and verify_certificate(n,R,H,caps,c,A):return Bound(0,0)
        return Bound(0,volume)
    def collective(A):
        y=contract(n,R,H,caps,A)
        return Bound(0,volume) if y is None else Bound(1,volume,y)
    lanes=[('normal',normal),('signed',signed),('character',character),('collective',collective)]
    if n-len(H)>12:lanes=[lanes[i] for i in (1,3,2,0)]
    for i,(name,f) in enumerate(lanes):
        try:
            A=Allowance(B,B.left//(len(lanes)-i))
            A.pay('partition_recovery_'+name)
            v=f(A)
            lo=max(v.lower,best.lower);hi=min(v.upper,best.upper)
            assert 0<=lo<=hi
            best=Bound(lo,hi,v.witness)
            if best.witness is not None:
                B.pay('partition_recovery_original_verify',1+n+sum(r.bit_count() for r in R))
                assert satisfies(best.witness,H,()) and all((r&best.witness).bit_count()<=c for r,c in zip(R,caps))
                return best
            if hi==0:return best
        except (ProbeLimit,Exhausted,RecursionError):
            # Even a witness whose verification cannot be charged is not paid.
            best=Bound(best.lower,best.upper)
    return best


def recover_frontier(n,R,H,caps,pending,upper,steps,B,signed_screen=False):
    """Demand-local recovery on the retained disjoint frontier, no restart.

    Only completed empty cells or sound upper bounds pay candidate volume.
    Any unprocessed cell retains its original volume. The sum is over
    disjoint original scopes, not over representations or proof branches.
    """
    lower=0
    for i,(P,I) in enumerate(reversed(pending)):
        if not B.left:break
        try:
            A=Allowance(B,B.left//(len(pending)-i))
            A.pay('partition_recovery_cell',1+len(P))
            v=recover_cell(n,R,P,caps,A,signed_screen=signed_screen)
            B.pay('partition_recovery_commit')
        except ProbeLimit:continue
        upper-= (1<<(n-len(P)))-v.upper
        lower+=v.lower
        assert 0<=lower<=upper
        if v.witness is not None:
            assert satisfies(v.witness,H,())
            return Bound(lower,upper,v.witness,steps)
    return Bound(lower,upper,None,steps)
