#!/usr/bin/env python3
"""Deterministic independent finite-Hubbard AFQMC smoke and negative controls."""
import json
import numpy as np
from qcafqmc_importance_phaseless_hubbard import run,setup

def main():
    H,T,ops,psi0,ground=setup()
    assert np.linalg.norm(T-ops.mean(axis=0))<1e-14
    assert abs(ground-np.linalg.eigvalsh(H)[0])<1e-13
    exact=psi0.copy()
    for _ in range(8):exact=T@exact
    reference=float((psi0@H@exact)/(psi0@exact))
    replicas=[run(seed=s,walkers=2400,steps=8,
                  branch_every=0)["final"]["absolute_error"] for s in (10,11,12,13)]
    assert np.mean(replicas)<.08
    good=run(seed=23,walkers=300,steps=8,complex_trial=True,
             phaseless=True,branch_every=0)["final"]["sampled_mixed_energy"]
    bad=run(seed=23,walkers=300,steps=8,complex_trial=True,
            phaseless=False,branch_every=0)["final"]["sampled_mixed_energy"]
    difference=abs(good-bad)
    assert difference>1e-7
    print(json.dumps({"scope":"finite Hubbard smoke, not original IonQ replication",
                      "exact_step8_mixed_energy":reference,
                      "four_seed_absolute_errors":replicas,
                      "mean_absolute_error":float(np.mean(replicas)),
                      "phaseless_vs_invalid_magnitude_only_delta":difference},indent=2))
if __name__=="__main__":
    main()
