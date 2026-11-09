#!/usr/bin/env python3
"""Reported classical cost arithmetic + strict original-data admission gate.

Attribution: Provazza, Knitter et al., arXiv:2611.08129 (2026);
Zhao et al., arXiv:2506.22408 (2025/2026).
No inferred AWS prices, no synthetic dataset promoted to experimental data.
"""
import argparse
import hashlib
import json
from pathlib import Path

REQUIRED=("measured_matchgate_shadows","active_space_integrals",
          "trial_state_circuit","model_checkpoint",
          "training_split","original_run_configuration")

def validate_manifest(name):
    if not name:
        return {"admissible":False,"missing":list(REQUIRED),
                "reason":"No original-source manifest"}
    path=Path(name).resolve()
    root=path.parent
    entries=json.loads(path.read_text())
    failures=[]
    for key in REQUIRED:
        x=entries.get(key)
        if not isinstance(x,dict):
            failures.append(key+": missing entry");continue
        if x.get("kind")!="original" or not x.get("source_url"):
            failures.append(key+": missing original provenance");continue
        if not x.get("path") or not x.get("sha256"):
            failures.append(key+": missing path/digest");continue
        f=(root/x["path"]).resolve()
        if not f.is_relative_to(root) or not f.is_file():
            failures.append(key+": missing or path escape");continue
        if hashlib.sha256(f.read_bytes()).hexdigest().lower()!=x["sha256"].lower():
            failures.append(key+": SHA256 mismatch")
    return {"admissible":not failures,"failures":failures}

def audit(manifest=None,gpu_hour_usd=None,cpu_core_hour_usd=None):
    old,new=90600.,596.
    r={"source":"arXiv:2611.08129, reported classical estimates per molecular structure",
       "prior_classical_usd":old,"new_classical_usd":new,
       "classical_saving_usd":old-new,
       "classical_saving_percent":100*(old-new)/old,
       "classical_cost_reduction_factor":old/new,
       "reported_old_gpu_hours":13200.,
       "reported_new_gpu_training_hours":4.,
       "reported_new_cpu_core_hours":6680.,
       "quantum_time_included":False,
       "original_data":validate_manifest(manifest)}
    if gpu_hour_usd is not None or cpu_core_hour_usd is not None:
        if gpu_hour_usd is None or cpu_core_hour_usd is None:
            raise ValueError("Supply both GPU and CPU rates")
        if min(gpu_hour_usd,cpu_core_hour_usd)<0:
            raise ValueError("Negative hourly rates")
        calc=4*gpu_hour_usd+6680*cpu_core_hour_usd
        r["rate_sensitivity"]={"hypothetical_new_usd":calc,
                "difference_from_reported_new_usd":calc-new,
                "old_gpu_at_supplied_rate_usd":13200*gpu_hour_usd,
                "rates_independently_verified":False}
    return r

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--manifest")
    p.add_argument("--gpu-hour-usd",type=float)
    p.add_argument("--cpu-core-hour-usd",type=float)
    a=p.parse_args()
    print(json.dumps(audit(a.manifest,a.gpu_hour_usd,a.cpu_core_hour_usd),indent=2))
