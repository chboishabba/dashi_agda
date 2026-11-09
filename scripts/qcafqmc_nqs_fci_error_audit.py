#!/usr/bin/env python3
"""Same-source NQS/FCI local-energy certificate.

Only small 8-orbital fixed-number sectors whose exact FCI reference can
actually be diagonalized. The exact FCI eigenstate is NOT asserted to be the
experimental upCCD reference or the original IonQ state.
"""
import argparse
import json
import numpy as np
from qcafqmc_molecular_fcidump import (parse_fcidump,fci_matrix,slater_amplitudes)
from qcafqmc_nqs_fci_same_source import trial_from_checkpoint
from qcafqmc_mixed_energy_error_certificate import (energy_certificate,
                                                       UncertifiableOverlap)

def audit(integrals,checkpoint,condition=1.e-12):
    h,eri,na,nb,core=parse_fcidump(integrals)
    if len(h)!=8:raise ValueError("expected 8 spatial orbitals")
    H,states=fci_matrix(h,eri,na,nb,core)
    if len(states)>5000:raise ValueError("exact reference sector too large")
    eig,vec=np.linalg.eigh(H)
    ideal=vec[:,0].astype(complex)
    learned,_=trial_from_checkpoint(checkpoint,states,len(h),na,nb)
    # Remove physically irrelevant global phase before comparing wavefunctions.
    inner=np.vdot(ideal,learned)
    if abs(inner)>condition:
        learned=learned*np.exp(-1j*np.angle(inner))
    he,orbitals=np.linalg.eigh(h)
    walker=slater_amplitudes(orbitals[:,:na],orbitals[:,:nb],states)
    certificate=energy_certificate(H,ideal,learned,walker,tolerance=condition)
    return {"scope":"same-Hamiltonian exact-FCI/NQS error certificate",
            "source_integrals":str(integrals),
            "model_checkpoint":str(checkpoint),
            "sector_dimension":len(states),
            "FCI_ground_energy":float(eig[0]),
            "physical_reference":"exact finite FCI ground state; NOT IonQ ideal upCCD",
            **certificate}

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("fcidump");p.add_argument("checkpoint")
    a=p.parse_args()
    try:
        print(json.dumps(audit(a.fcidump,a.checkpoint),indent=2))
    except UncertifiableOverlap as error:
        raise SystemExit("FAIL-CLOSED: "+str(error)) from error
