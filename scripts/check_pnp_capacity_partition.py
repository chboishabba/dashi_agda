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


def partition(n,R,H,caps,B,nodes=32,fanout=128,closure=True):
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
            # Reuse original one-hot affine hull, not auxiliary duplicated columns.
            if closure and all(c==1 for c in caps):
                from check_pnp_exact_cover_pair_hull import close
                try:
                    Q,y=close(n,R,Allowance(B,B.left//4),pairs=False,required=P)
                except ProbeLimit:Q,y=P,None
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
            cells=row_cells(n,P,R[i],caps[i],B,fanout)
            if cells is None:break
            J=tuple(j for j in I if j!=i)
            # Transaction: charge before changing frontier or mass.
            B.pay('row_partition_commit',1+len(cells)*(1+len(J)))
            upper+=sum(1<<(n-len(Q)) for Q in cells)-(1<<(n-len(P)))
            pending.pop();pending.extend((Q,J) for Q in reversed(cells))
        except ProbeLimit:break
    assert upper>=0
    return Bound(0,upper,None,steps)
