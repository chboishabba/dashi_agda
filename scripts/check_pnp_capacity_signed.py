"""Progressive paired signed mass on ORIGINAL capacity coordinates.

The lower polynomial is a masked forest, the upper polynomial is the
indicator of avoiding only the promoted events. Both share one chart and
one promotion history. Refusals retain bounds, never certify emptiness.
"""
from dataclasses import dataclass
from fractions import Fraction
from check_pnp_affine_normal_components import canon,chart,lift,restrict,satisfies
from check_pnp_normal_boundary_join import value
from check_pnp_adaptive_signed_escape import add,intersect,forest,masked
from check_pnp_partial_quotient import mass,positive_point
from check_pnp_capacity_geometry import violation_flats
from check_pnp_demand_strata import Allowance,ProbeLimit


@dataclass(frozen=True)
class Bound:
    lower:int
    upper:int
    witness:object=None
    stage:int=0


def pull(Q,u,V,B):
    T={}
    B.pay('capacity_signed_pull',1+sum(len(A)+1 for A in Q)*(1+len(V)))
    for A,w in Q.items():
        add(T,canon((value(V,a),b^((a&u).bit_count()%2)) for a,b in A),w)
    return T


def reopen_mass(n,R,H,caps,u,V,P,L,B):
    """The donor's positive-point continuation on the demanded affine fibre."""
    v,W=chart(len(V),P)
    T=pull(L,v,W,B)
    q=positive_point(len(W),T,(),B)
    if q is None:return None
    y=lift(u,V,lift(v,W,q[0]))
    B.pay('capacity_signed_original_verify',1+n+sum(r.bit_count() for r in R))
    assert satisfies(y,H,()) and all((r&y).bit_count()<=c for r,c in zip(R,caps))
    return y


def observe(n,R,H,caps,B,normal=None,promotions=8,terms=256):
    """One bound (whole demand) or two bounds (complementary normal fibres).
    A positive lower integral can reopen a witness, even without a positive
    minimum. All sums are integer counts on original points.
    """
    assert H==canon(H) and canon(H+tuple((r,1) for r in R))==H
    assert len(R)==len(caps)
    absolute=[H] if normal is None else [canon(H+((normal,b),)) for b in (0,1)]
    bounds=[Bound(0,0 if h is None else 1<<(n-len(h))) for h in absolute]
    if any(c<1 for c in caps):return tuple(Bound(0,0) for h in absolute)
    try:
        B.pay('capacity_signed_chart',1+n*(1+len(H))**2)
        u,V,E=restrict(n,H,violation_flats(n,R,H,caps,B),B)
        d=len(V)
        pins=[()] if normal is None else [canon(((value(V,normal),b^((normal&u).bit_count()%2)),)) for b in (0,1)]
        if () in E:return tuple(Bound(0,0) for p in pins)
        # A cheap upper bound precedes the more costly overlap construction.
        for i,p in enumerate(pins):
            if p is None:continue
            N=1<<(d-len(p))
            B.pay('capacity_signed_single_events',1+len(E)*(1+d)**2)
            from check_pnp_collective_fibre_escape import size
            hi=N-max((size(A,d,p) for A in E),default=0)
            bounds[i]=Bound(0,hi)
        if all(b.upper==0 for b in bounds):return tuple(bounds)
        B.pay('capacity_signed_forest_prepare',1+len(E)**2*(1+d))
        T=forest(E,d,B);R0=set(range(len(E)));Q={():1}
        order=sorted(R0,key=lambda i:(len(E[i]),-sum(i in (a,b) for a,b,_ in T),i))
        for stage in range(min(promotions,len(E))+1):
            # Preflight the largest possible masked expression before forming it.
            B.pay('capacity_signed_stage',1+len(Q)*(1+len(R0)+len(T))*(1+d))
            L=masked(Q,E,R0,T,B)
            if len(L)>terms:break
            for i,p in enumerate(pins):
                if p is None:continue
                old=bounds[i]
                B.pay('capacity_signed_integrate',1+(len(L)+len(Q))*(1+d)**2)
                lo=max(old.lower,0,mass(d,L,p,B))
                hi=min(old.upper,mass(d,Q,p,B))
                assert 0<=lo<=hi
                bounds[i]=Bound(lo,hi,old.witness,stage)
                if lo>0 and old.witness is None:
                    # Reopen from the CURRENT polynomial only if its own
                    # integral is positive (an earlier stage may be stronger).
                    if mass(d,L,p,B)>0:
                        try:
                            w=reopen_mass(n,R,absolute[i],caps,u,V,p,L,Allowance(B,B.left//2))
                            if w is not None:bounds[i]=Bound(lo,hi,w,stage)
                        except ProbeLimit:pass
            if any(b.witness is not None for b in bounds) or all(b.lower==b.upper for b in bounds):break
            if stage==min(promotions,len(E)):break
            i=order[stage]
            B.pay('capacity_signed_promote',1+len(Q)*(1+d))
            P=dict(Q);intersect(Q,E[i],-1,B,P)
            if len(P)>terms:break
            Q=P;R0.remove(i)
    except ProbeLimit:pass
    return tuple(bounds)


def relative(bounds):
    """Contrast interval conditional on positive total; None if empty."""
    a,b=bounds
    if a.upper+b.upper==0:return None
    if b.upper==0:return Fraction(1),Fraction(1)
    if a.upper==0:return Fraction(-1),Fraction(-1)
    return (Fraction(a.lower-b.upper,a.lower+b.upper),
            Fraction(a.upper-b.lower,a.upper+b.lower))


def select(bounds,inhabited=False):
    a,b=bounds
    if a.lower or b.lower:return int(b.lower>a.lower)
    if not inhabited:return None
    D=relative(bounds)
    if D is None:return None
    if D[0]>=0:return 0
    if D[1]<=0:return 1
    return None


def merge(a,b):
    """Disjoint original cells only; never add overlapping observations."""
    return Bound(a.lower+b.lower,a.upper+b.upper,
                 a.witness if a.witness is not None else b.witness,
                 max(a.stage,b.stage))


def observe_ledger(L,H,caps,normal,B,cell_cap=128,leaf_cap=8,seam_cap=8):
    """Use the existing disjoint exclusion ledger, paired signed integrals,
    then exact separator counts where affordable. No independent clock.
    """
    from check_pnp_demand_strata import bounded_fold
    H,caps=L._demand(H,caps)
    if H is None:return Bound(0,0),Bound(0,0)
    cells=L.remaining(H,caps,B,cell_cap)
    out=[Bound(0,0),Bound(0,0)]
    for j,Q in enumerate(cells):
        A=Allowance(B,B.left//(len(cells)-j))
        I=observe(L.n,L.R,Q,caps,Allowance(A,A.left//2),normal)
        for b,v in enumerate(I):
            P=canon(Q+((normal,b),))
            if P is not None and v.lower!=v.upper and v.witness is None:
                try:
                    z=bounded_fold(L.n,L.R,P,caps,Allowance(A,A.left//(2-b)),leaf_cap,seam_cap)
                    if z is not None:v=Bound(z[0],z[0],z[1],v.stage)
                except ProbeLimit:pass
            out[b]=merge(out[b],v)
    return tuple(out)
