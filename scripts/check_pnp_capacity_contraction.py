"""Original capacity demands through existing Rado/collective/signed consumers.

This is a constructive bypass: an inconclusive or empty result from these
donors is not a replayable character exclusion and is not recorded as one.
The original odd-parity carrier and absolute column identities are retained.
"""
from itertools import combinations
from math import comb
from check_pnp_affine_normal_components import bits, canon, satisfies
from check_pnp_demand_strata import Allowance,ProbeLimit


def contract(n,R,H,caps,B):
    assert H==canon(H) and canon(H+tuple((r,1) for r in R))==H
    assert len(R)==len(caps)
    if any(c<1 for c in caps):return None
    # The smallest forbidden count defines a union of affine subset events.
    # Under retained odd parity an even threshold can also be raised by one.
    F=[]
    for r,c in zip(R,caps):
        J=list(bits(r));k=c+1
        if k%2==0 and k+1<=len(J) and comb(len(J),k+1)<comb(len(J),k):k+=1
        if k>len(J):continue
        B.pay('capacity_contraction_events',comb(len(J),k)*(1+k))
        F.extend(tuple((1<<j,1) for j in T) for T in combinations(J,k))
    F=tuple(sorted(set(F)))
    from check_pnp_adaptive_signed_escape import adaptive
    from check_pnp_collective_fibre_escape import solve
    for i,producer in enumerate((adaptive,solve)):
        try:
            A=Allowance(B,max(0,B.left//(2-i)))
            y,_,done=producer(n,H,F,A.left,budget=A)
            if y is not None:
                B.pay('capacity_contraction_reopen',1+n+sum(r.bit_count() for r in R))
                assert done and satisfies(y,H,()) and all((r&y).bit_count()<=c for r,c in zip(R,caps))
                return y
        except (ProbeLimit,RecursionError):pass
    return None
