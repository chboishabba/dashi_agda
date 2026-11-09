#!/usr/bin/env python3
"""Same-object 16-spin-orbital NQS / Slater / electronic-Hamiltonian check.

Builds the *same* fixed-particle occupation sector and exact FCI Hamiltonian
as qcafqmc_molecular_fcidump.py. This finite-space bridge has explicit
exponential cost, not a scalable iPie neural-trial implementation.

Attribution: Provazza, Knitter et al., arXiv:2611.08129; standard Slater
second quantization; DASHI atomic/369 generator owner.
"""
import argparse
import json
from pathlib import Path
import numpy as np
import torch
from qcafqmc_molecular_fcidump import (fci_matrix,parse_fcidump,
                                        slater_amplitudes)
from qcafqmc_fixed_sector_transformer import AutoregressiveNQS

def occupation_rows(states,n):
    if n!=8:raise ValueError("16 spin orbital NQS requires 8 spatial orbitals")
    return np.array([[(state>>i)&1 for i in range(2*n)]
                     for state in states],dtype=np.int64)

def trial_from_checkpoint(checkpoint,states,n,na,nb):
    data=torch.load(checkpoint,map_location="cpu",weights_only=True)
    if int(data["n_alpha"])!=na or int(data["n_beta"])!=nb:
        raise ValueError("checkpoint electron sector differs from Hamiltonian")
    model=AutoregressiveNQS()
    model.load_state_dict(data["weights"])
    model.eval()
    with torch.no_grad():
        config=torch.from_numpy(occupation_rows(states,n))
        amplitudes=model(config,na,nb).numpy().astype(complex)
    norm=np.linalg.norm(amplitudes)
    if not np.isfinite(norm) or norm<=1e-12:
        raise ValueError("invalid learned trial state")
    return amplitudes/norm,model

def walker_mixed_energy(H,trial,walker,conditioning=1e-9):
    den=np.vdot(trial,walker)
    if abs(den)<conditioning:
        raise ValueError("ill-conditioned trial / walker overlap")
    return np.vdot(trial,H@walker)/den

def run(fcidump,checkpoint):
    h,eri,na,nb,core=parse_fcidump(fcidump)
    if len(h)!=8:raise ValueError("expected eight spatial orbitals")
    H,states=fci_matrix(h,eri,na,nb,core)
    if len(states)>5000:raise ValueError("finite FCI sector too large")
    trial,_=trial_from_checkpoint(checkpoint,states,len(h),na,nb)
    # Deterministic noninteracting occupied-orbital trial walker.
    ev,orbitals=np.linalg.eigh(h)
    alpha=orbitals[:,:na];beta=orbitals[:,:nb]
    walker=slater_amplitudes(alpha,beta,states)
    overlap=np.vdot(trial,walker)
    local=walker_mixed_energy(H,trial,walker)
    energy=float(np.linalg.eigvalsh(H)[0])
    result={"scope":"same-source finite 16-qubit neural trial / molecular FCI bridge",
            "integrals":str(fcidump),
            "checkpoint":str(checkpoint),
            "sector_size":len(states),
            "trial_norm":float(np.linalg.norm(trial)),
            "walker_norm":float(np.linalg.norm(walker)),
            "trial_walker_overlap_real":float(overlap.real),
            "trial_walker_overlap_imag":float(overlap.imag),
            "local_energy_real":float(local.real),
            "local_energy_imag":float(local.imag),
            "exact_sector_ground_energy":energy,
            "scalable_nqs_ipie_trial":False,
            "original_ionq_shadow_checkpoint_verified":False}
    return result

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("fcidump")
    p.add_argument("nqs_checkpoint")
    a=p.parse_args()
    print(json.dumps(run(a.fcidump,a.nqs_checkpoint),indent=2))
