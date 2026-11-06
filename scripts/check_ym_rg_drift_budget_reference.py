#!/usr/bin/env python3
"""Exact rational reference for source-written RG telescoping q bound.

Illustrative arithmetic only; not an SU(N) RG/physical/Agda receipt.
"""
from fractions import Fraction as Q
import json

def verify(q0, amplitude, ratio, n=128):
    assert Q(0) <= q0 and Q(0) <= amplitude and Q(0) <= ratio < 1
    budget = amplitude/(1-ratio)
    q = q0+budget
    assert q < 1, 'no uniform contraction margin'
    kappa = q0
    finite_drift = Q(0)
    for i in range(n):
        assert kappa <= q0+finite_drift <= q
        increment = amplitude*ratio**i
        finite_drift += increment
        kappa += increment
        assert kappa <= q0+finite_drift <= q
        assert 2**i * Q(1,2**i) == 1
    assert finite_drift == budget*(1-ratio**n)
    return q, finite_drift

def selftest():
    q, finite=verify(Q(1,3),Q(1,12),Q(1,2))
    assert q == Q(1,2)
    assert q-finite == Q(1,3) + Q(1,6)*Q(1,2)**128
    failures=0
    for args in [(Q(9,10),Q(1,5),Q(1,2)),
                 (Q(1,3),Q(-1,12),Q(1,2)),
                 (Q(1,3),Q(1,12),Q(1)),
                 (Q(1,3),Q(1,12),Q(-1,2))]:
        try: verify(*args)
        except AssertionError: failures+=1
    assert failures == 4
    assert all(0 < (1-Q(1,2**n)) < 1 for n in range(1,129))
    return {'status':'PASS','exact_q':str(q),'strict_gap_fraction':str(1-q),
            'finite_drift_128':str(finite), 'refinement_stages':128,
            'negative_controls':5,
            'physical_original_wilson_RG_error_bound':'NOT_PROVED',
            'agda_kernel_receipt':'NOT_AVAILABLE'}

if __name__=='__main__': print(json.dumps(selftest(), indent=2))
