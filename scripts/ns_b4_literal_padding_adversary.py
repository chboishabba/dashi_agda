#!/usr/bin/env python3
"""Exact cutoff-padding negative control for literal R440 B4.

Physical real transverse seed: u_hat(±e_x)=u_hat(±e_y)=e_z.
At output k=e_x+e_y only active ordered cells (e_x,e_y), (e_y,e_x)
are core, with H+ cross H- values (-i/4,-i/4,±1/4).
Hence M=(-i/2,-i/2,0), ||M||²=1/2, r_active=2.

The FULL output-fibre R440 noncore/core covariance includes ZERO velocity
incidences in n_noncore and the rate sum. Defect is exactly
  sum_(p in noncore) (|p|²+|k-p|²-2).
The literal Young core/core companion mass is computed from ALL core pairs,
including zero-zero pairs; it becomes fixed for N>=9.

Source definitions: PhysicalParabolicCriticalRegionRoutingExact,
PhysicalCriticalTouchingDefectNoncoreCore20261007Exact,
PhysicalCriticalTouchingLiteralCompanion20261007Exact and
PhysicalCriticalTouchingDefectR44020261007Exact.

This falsifies cutoff-uniform payment if local ED of this unchanged physical
state stays uniformly bounded. A free cutoff-dependent 'localED' record
input is NOT such a bound. No Clay claim or kernel certification.
"""
from fractions import Fraction
from itertools import product
import argparse
import json

P=(1,0,0)
Q=(0,1,0)
K=(1,1,0)

def shell(p):
    m=max(map(abs,p))
    return 0 if m <= 1 else (m-1).bit_length()

def region(p,q):
    a,b,c=shell(p),shell(q),shell(K)
    if a+3 < b: return "noncore" if 3*a <= 2*b else "core"
    if b+3 < a: return "noncore" if 3*b <= 2*a else "core"
    if c+3 < a and c+3 < b:
        return "noncore" if 5*c <= 4*max(a,b) else "core"
    return "core"

def certificate(N):
    if N < 1: raise ValueError("cutoff must be positive")
    core,noncore=[],[]
    for p in product(range(-N,N+1),repeat=3):
        q=tuple(K[j]-p[j] for j in range(3))
        if max(map(abs,q))>N:continue
        rate=sum(x*x for x in p+q)
        (core if region(p,q)=="core" else noncore).append((p,rate))
    assert sorted(p for p,r in core if p in (P,Q))==sorted((P,Q))
    assert all(p not in (P,Q) for p,r in noncore)
    nN=len(noncore)
    rN=sum(rate for _,rate in noncore)
    # w_(active ordered cell)=2Re<M,A>=1/2; all noncore w=0.
    defect=Fraction(rN-2*nN)
    # ||M||²=1/2, ||A||²=||B||²=3/16, r_A=r_B=2.
    zeros=sorted(r for p,r in core if p not in (P,Q))
    count=len(zeros)
    zero_zero=sum((2*i-count+1)*rate for i,rate in enumerate(zeros))
    active_zero=2*Fraction(11,8)*sum(abs(rate-2) for rate in zeros)
    companion=Fraction(zero_zero)+active_zero
    assert defect>=0
    return {
        "cutoff":N,"output":K,"core_rows":len(core),
        "noncore_zero_amplitude_rows":nN,
        "noncore_rate_sum":rN,
        "signed_defect":str(defect),
        "literal_core_companion":str(companion),
        "defect_over_companion":str(defect/companion) if companion else None,
        "defect_exceeds_half_companion":bool(2*defect>companion),
    }

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--cutoffs",nargs="+",type=int,default=[4,8,9,16,24,36,40])
    ns=ap.parse_args().cutoffs
    results=[certificate(n) for n in ns]
    for r in results:
        if r["cutoff"]>=9:
            assert r["core_rows"]==5474
            assert r["literal_core_companion"]=="1345859672"
    print(json.dumps({
        "schema":"ns.r440.zero-padding.v1",
        "state":"u_hat(±e_x)=u_hat(±e_y)=e_z; all other modes zero",
        "seed_is_real_transverse":True,
        "physical_helical_reciprocals_at_active_modes": "1,1",
        "normalization":"full ordered physical output fibre, zero cells retained",
        "physical_shear_solution":"u(t,x,y,z)=2*exp(-t)*(cos(x)+cos(y))*e_z on 2pi-periodic torus; pressure constant",
        "nonlinear_physical_forcing":"zero identically",
        "padding_invariant_modal_M":"(-i/2,-i/2,0)",
        "padding_invariant_R440_weighted_amplitude":"2*M",
        "padding_invariant_modal_coherent_heat_work":"2",
        "output_heat_centered_R440_work":"0",
        "not_claimed":["Clay B false","kernel proof","cutoff-growing ED ruled out"],
        "cutoffs":results,
    },indent=2))

if __name__=="__main__":
    main()
