#!/usr/bin/env python3
"""Multi-seed Hubbard auxiliary-field sampling convergence audit.

No single-seed cutoff is taken as a statistical confidence interval.
Reference: Hirsch 1983 HS; Provazza, Knitter et al. arXiv:2611.08129.
"""
import json
import numpy as np
from qcafqmc_multistep_hubbard import run

out=[]
for n in (2000,10000,50000):
    trials=[run(seed=s,samples=n,validate=False)["history"][-1] for s in range(11,21)]
    e=np.array([v["energy_error"] for v in trials])
    state=np.array([v["state_l2_error"] for v in trials])
    out.append({"samples":n,"seeds":list(range(11,21)),
        "mean_absolute_mixed_energy_error":float(e.mean()),
        "mixed_energy_error_rmse":float(np.sqrt(np.mean(e**2))),
        "mean_state_l2_error":float(state.mean())})
print(json.dumps({"scope":"small-Hubbard 10-seed convergence, not nickel",
                  "results":out},indent=2))
assert out[-1]["mixed_energy_error_rmse"] < out[0]["mixed_energy_error_rmse"]
assert out[-1]["mean_state_l2_error"] < out[0]["mean_state_l2_error"]
