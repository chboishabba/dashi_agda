"""Capacity-scoped character certificates and original binary mass intervals.

This is an adapter, not a new elimination engine. All bounds count ORIGINAL
points, never count paths in the auxiliary affine relaxation. A refusal is
UNKNOWN. The existing Budget/Allowance is the only clock.
"""
from dataclasses import dataclass
from itertools import combinations
from math import comb
from fractions import Fraction
from check_pnp_affine_normal_components import bits, canon, chart, satisfies
from check_pnp_normal_boundary_join import value
from check_pnp_character_ideal import exclude, compact, verify, source_shifts
from check_p0_affine_forest_20261125 import mass, forest, score


def capacity_chart(n, R, H, caps, B):
    """One-hot transitions with parity glue; one extension per admissible x.

    The affine chart ALONE need not be parsimonious: the one-hot rows are
    essential. H is the original absolute demand including source parity.
    """
    assert len(R)==len(caps) and H==canon(H)
    assert canon(H+tuple((r,1) for r in R))==H
    if any(c<1 for c in caps): return None  # original odd parity
    equations=list(H); F=[]; paths=[]; N=n
    for r,c in zip(R,caps):
        J=list(bits(r)); d=len(J); c=min(c,d)
        if c==d: continue
        if c==1:
            B.pay('capacity_onehot',1+d)
            F.append(tuple((1<<j,0) for j in J)); continue
        prev={0:0}; layers=[]
        for i,j in enumerate(J):
            transitions=[]; incoming={}; outgoing={}; chosen=0
            for k in range(min(i,c)+1):
                for b in (0,1):
                    if k+b>c: continue
                    B.pay('capacity_transition',1+N)
                    s=1<<N; N+=1
                    transitions.append((k,b,s))
                    outgoing[k]=outgoing.get(k,0)^s
                    incoming[k+b]=incoming.get(k+b,0)^s
                    if b: chosen^=s
            row=tuple((s,0) for k,b,s in transitions)
            F.append(row)
            equations.append((sum(s for k,b,s in transitions),1))
            equations.append((chosen^(1<<j),0))
            if i:
                for k in sorted(set(prev)|set(outgoing)):
                    equations.append((prev.get(k,0)^outgoing.get(k,0),0))
            else:
                equations.append((outgoing.get(0,0),1))
            prev=incoming; layers.append((j,tuple(transitions)))
        paths.append(tuple(layers))
    B.pay('capacity_chart_affine',1+N*(1+len(equations))**2)
    P=canon(equations)
    return N,P,tuple(F),tuple(paths)


def extend_original(x, C):
    """Reverse receipt for the unique one-hot count path."""
    N,P,F,paths=C
    if P is None: return None
    y=x
    for layers in paths:
        k=0
        for j,T in layers:
            b=x>>j&1
            s=next((s for a,v,s in T if (a,v)==(k,b)),None)
            if s is None: return None
            y|=s; k+=b
    return y if satisfies(y,P,()) and all(sum((s&y).bit_count()%2^b for s,b in G)==1 for G in F) else None


def pullback(C,B):
    N,P,F,_=C
    u,V=chart(N,P)
    B.pay('capacity_character_pullback',1+sum(map(len,F))*(1+len(V)))
    return tuple(tuple((value(V,s),b^((s&u).bit_count()%2)) for s,b in G) for G in F)


@dataclass(frozen=True)
class Certificate:
    # Scope is bound by the receiving Ledger (n,R,H,caps).
    kind: str
    proof: tuple=()
    prime: int=3
    normal: int=0
    children: tuple=()


def verify_certificate(n,R,H,caps,cert,B):
    """Replay a factorized demand exclusion; no projector expansion.

    The leaf proves 1=0 on the unique-extension chart of H. Hence the
    original indicator I_H vanishes on feasible points. A sibling node
    uses I_H=I_(H,a=0)+I_(H,a=1), not an expanded character dictionary.
    """
    B.pay('capacity_certificate_node',1+len(H)+len(caps))
    if cert.kind=='siblings':
        if len(cert.children)!=2 or not 0<cert.normal<1<<n: return False
        Q=[canon(H+((cert.normal,b),)) for b in (0,1)]
        return all(q is not None and len(q)==len(H)+1 and
                   verify_certificate(n,R,q,caps,k,B)
                   for q,k in zip(Q,cert.children))
    C=capacity_chart(n,R,H,caps,B)
    if cert.kind=='affine_empty': return C is None or C[1] is None
    if cert.kind!='character' or C is None or C[1] is None: return False
    return verify(pullback(C,B),cert.proof,cert.prime,B=B)


def discover_certificate(n,R,H,caps,B,degree=1,max_pivots=256):
    C=capacity_chart(n,R,H,caps,B)
    if C is None or C[1] is None: return Certificate('affine_empty')
    F=pullback(C,B)
    proof=exclude(F,source_shifts(F,degree,B),3,B,max_pivots=max_pivots)
    return None if proof is None else Certificate('character',compact(proof,B))


def mass_interval(n,R,H,caps,B):
    """Forest lower and single-event upper bounds on ORIGINAL integer mass.

    A cap violation is a union of affine all-one subset events. Charge
    their combinatorial size BEFORE generating any events. High-cap rows
    may refuse; no additive estimate of auxiliary mass is substituted.
    """
    assert H==canon(H) and len(R)==len(caps)
    assert canon(H+tuple((r,1) for r in R))==H
    if any(c<1 for c in caps): return 0,0,(),()
    from check_pnp_capacity_geometry import violation_flats
    E=violation_flats(n,R,H,caps,B); m=len(E)
    B.pay('capacity_forest_pairs',1+(1+m*m)*(1+n+len(H))**3)
    events=[list(e) for e in E]; pins=list(H); edges=tuple(forest(events,pins))
    size=1<<(n-len(H))
    lo=max(Fraction(0),score(events,edges,pins))*size
    hi=(1-max((mass(e,pins) for e in events),default=Fraction(0)))*size
    assert lo.denominator==hi.denominator==1 and 0<=lo<=hi<=size
    return int(lo),int(hi),E,edges


def reopen_positive(n,R,H,caps,interval,B):
    """Use the donor's fixed forest averaging, in original coordinates."""
    lo,hi,E,edges=interval
    if lo<=0: return None
    events=[list(e) for e in E]; Q=H
    while len(Q)<n:
        piv={a.bit_length()-1 for a,b in Q}
        a=1<<next(i for i in range(n) if i not in piv)
        B.pay('capacity_forest_descent',2*(1+len(E)+len(edges))*(1+n)**3)
        children=[canon(Q+((a,b),)) for b in (0,1)]
        vals=[score(events,edges,list(q)) for q in children]
        assert max(vals)>0
        Q=children[int(vals[1]>vals[0])]
    x=chart(n,Q)[0]
    B.pay('capacity_original_verify',1+n+sum(r.bit_count() for r in R))
    assert satisfies(x,H,()) and all((r&x).bit_count()<=c for r,c in zip(R,caps))
    return x


def signed_interval(n,R,H,caps,a,B):
    """Binary ORIGINAL mass contrast; both orientations retained."""
    Q=[canon(H+((a,b),)) for b in (0,1)]
    I=[(0,0,(),()) if q is None else mass_interval(n,R,q,caps,B) for q in Q]
    l0,u0=I[0][:2]; l1,u1=I[1][:2]
    return Q,I,(l0-u1,u0-l1)


def preferred_child(I,delta,inhabited=False):
    """No choice from a relative sign unless habitation is certified."""
    if I[0][0]>0 or I[1][0]>0: return int(I[1][0]>I[0][0])
    if inhabited:
        if I[0][1]==0 or delta[1]<=0: return 1
        if I[1][1]==0 or delta[0]>=0: return 0
    return None
