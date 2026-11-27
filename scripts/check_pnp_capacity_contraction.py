"""Shared-clock capacity contraction via existing signed and collective donors."""
from check_pnp_affine_normal_components import canon,satisfies
from check_pnp_demand_strata import Allowance,ProbeLimit
from check_pnp_capacity_geometry import violation_flats


def admissible_floor(M,n,H,B):
    """Two sound domain-conditioned floors, with complementary allowances."""
    from check_pnp_adaptive_signed_escape import lower
    from check_pnp_grouped_quotient_floor import conditioned
    from check_pnp_partial_quotient import conflict_floor
    best=lower(M)
    if best>0:return best
    pool=Allowance(B,B.left//2)  # reserve the remainder for absorption/reopening
    for i,producer in enumerate((conditioned,conflict_floor)):
        try:
            A=Allowance(pool,pool.left//(2-i))
            best=max(best,producer(M,n,H,A))
            if best>0:return best
        except ProbeLimit:pass
    return best


def contract(n,R,H,caps,B):
    assert H==canon(H) and canon(H+tuple((r,1) for r in R))==H
    assert len(R)==len(caps)
    if any(c<1 for c in caps):return None
    F=violation_flats(n,R,H,caps,B)
    from check_pnp_adaptive_signed_escape import adaptive
    from check_pnp_collective_fibre_escape import solve
    from check_pnp_partial_quotient import solve as partial
    for i,producer in enumerate((adaptive,partial,solve)):
        try:
            A=Allowance(B,max(0,B.left//(3-i)))
            kw={'admissible_envelope':admissible_floor} if i==0 else {}
            y,_,done=producer(n,H,F,A.left,budget=A,**kw)
            if y is not None:
                B.pay('capacity_contraction_reopen',1+n+sum(r.bit_count() for r in R))
                assert done and satisfies(y,H,()) and all((r&y).bit_count()<=c for r,c in zip(R,caps))
                return y
        except (ProbeLimit,RecursionError):pass
    return None
