#!/usr/bin/env python3
"""Exact rational B4 bipartite covariance cancellation and oscillation bounds.

For each noncore/core pair, covariance is
    (r_i-r_j)(w_i-w_j).
The signed B4 work is the *negative* sum of these pair products.
This is a finite algebraic analysis, NOT the missing cutoff-uniform
physical estimate or the canonical B4 payment itself.
"""
from fractions import Fraction as Q
from itertools import product

def covariance(noncore, core):
    return sum(((r-s)*(v-w) for r,v in noncore for s,w in core),Q(0))

def four_moments(noncore,core):
    n,c=Q(len(noncore)),Q(len(core))
    rn=sum((r for r,_ in noncore),Q(0))
    rc=sum((r for r,_ in core),Q(0))
    wn=sum((v for _,v in noncore),Q(0))
    wc=sum((v for _,v in core),Q(0))
    rwn=sum((r*v for r,v in noncore),Q(0))
    rwc=sum((r*v for r,v in core),Q(0))
    return c*rwn+n*rwc-rn*wc-rc*wn

def oscillation_envelope(noncore,core):
    """Sharp termwise triangle envelope, independent of common rate shifts."""
    return sum((abs(r-s)*abs(v-w) for r,v in noncore for s,w in core),Q(0))

def range_l1_envelope(noncore,core):
    """rate oscillation sup times sum of absolute work differences."""
    osc=max((abs(r-s) for r,_ in noncore for s,_ in core),default=Q(0))
    workdiff=sum((abs(v-w) for _,v in noncore for _,w in core),Q(0))
    return osc*workdiff

def certificate(noncore,core):
    exact=covariance(noncore,core)
    normal=four_moments(noncore,core)
    tight=oscillation_envelope(noncore,core)
    loose=range_l1_envelope(noncore,core)
    if not exact==normal or not abs(exact)<=tight<=loose:
        raise AssertionError("finite B4 algebra or bound failed")
    return {
        "covariance":str(exact),
        "negative_defect":str(-exact),
        "oscillation_envelope":str(tight),
        "range_l1_envelope":str(loose),
        "identity_exact":True,
        "negative_defect_bounded":True,
    }

def exhaustive_small():
    vals=[Q(-1),Q(0),Q(1)]
    cells=list(product(vals,vals))
    cases=0
    for a in cells:
        for b in cells:
            for c in cells:
                certificate((a,b),(c,))
                cases+=1
    return cases

if __name__=="__main__":
    print("exact finite B4 certificates",exhaustive_small())
