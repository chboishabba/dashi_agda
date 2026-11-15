#!/usr/bin/env python3
"""Finite CI export basis/order/phase regression, without needing ipie.

Uses a mock NQS amplitude evaluator so the test isolates the adapter,
the exact occupation order, global phase, and no coefficient truncation.
It is NOT an original IonQ checkpoint or chemistry result.
"""
from itertools import combinations
from unittest.mock import patch
import numpy as np
from qcafqmc_molecular_fcidump import sector
from qcafqmc_nqs_ipie_particle_hole import export_particle_hole

def test_same_sector_export():
    states=sector(8,1,1)
    rng=np.random.default_rng(42)
    exact=rng.normal(size=len(states))+1j*rng.normal(size=len(states))
    exact/=np.linalg.norm(exact)
    with patch("qcafqmc_nqs_ipie_particle_hole.trial_from_checkpoint",
               return_value=(exact,None)):
        ci,occ_a,occ_b=export_particle_hole("synthetic-model",8,1,1)
    assert ci.shape==(64,)
    assert occ_a.shape==(64,1) and occ_b.shape==(64,1)
    assert np.all(np.diff(abs(ci))<=1e-12)
    for k in range(len(ci)):
        state=(1<<int(occ_a[k,0]))|(1<<(8+int(occ_b[k,0])))
        original_index=states.index(state)
        assert np.allclose(ci[k],exact[original_index])
    assert abs(np.vdot(ci,ci)-1)<1e-12
    assert np.max(abs(ci))>0
    with patch("qcafqmc_nqs_ipie_particle_hole.trial_from_checkpoint",
               return_value=(exact,None)):
        try:export_particle_hole("synthetic-model",8,1,1,max_determinants=10)
        except ValueError:pass
        else:raise AssertionError("determinant budget was bypassed")
    return True

if __name__=="__main__":
    assert test_same_sector_export()
    print("PASS: full 64-determinant fixed-sector NQS/CI order, phase and budget")
