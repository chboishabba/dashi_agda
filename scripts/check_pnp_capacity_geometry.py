"""Parity-conditioned original forbidden flats (shared by capacity consumers)."""
from itertools import combinations
from math import comb
from check_pnp_affine_normal_components import bits, canon


def violation_flats(n,R,H,caps,B):
    """Original coordinates; exact union ON H, including the odd zero mode.
    Choose the smaller of adjacent equivalent threshold representations.
    Charge before expanding; an unaffordable expansion is a refusal.
    """
    assert H==canon(H) and canon(H+tuple((r,1) for r in R))==H
    assert len(R)==len(caps)
    if any(c<1 for c in caps):return ((),)
    F=[]
    for r,c in zip(R,caps):
        J=tuple(bits(r));d=len(J);k=c+1
        if k%2==0:
            # The next odd count is the first possible violating count.
            if k+1>d:continue
            if comb(d,k+1)*(k+2)<=comb(d,k)*(k+1):k+=1
        if k>d:continue
        B.pay('capacity_violation_events',comb(d,k)*(1+k))
        F.extend(tuple((1<<j,1) for j in T) for T in combinations(J,k))
    return tuple(sorted(set(F)))
