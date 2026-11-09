#!/usr/bin/env python3
"""Full finite-sector NQS -> iPie ParticleHole trial without state refitting.

Converts a trained 16-qubit fixed-particle NQS into the same ordered 8-orbital
Slater-occupation CI basis used by DASHI FCI. iPie subsequently evaluates
force bias and local energy using its own, tested multi-determinant code.

Reference: ipie 0.7.1 docs, "Multi-determinant trials"/ParticleHole.
This is an *exact but exponentially costly* finite-sector export, not an
efficient 13k-parameter neural trial oracle. No device data is supplied.
"""
from math import comb
import hashlib
from pathlib import Path
import numpy as np
from qcafqmc_molecular_fcidump import sector
from qcafqmc_nqs_fci_same_source import trial_from_checkpoint

def export_particle_hole(checkpoint, n_spatial, n_alpha, n_beta,
                         cutoff=0., max_determinants=5000):
    if n_spatial!=8:raise ValueError("fixed 16-spin-orbital NQS requires 8 spatial orbitals")
    if not (0<=n_alpha<=8 and 0<=n_beta<=8):
        raise ValueError("invalid electron sector")
    expected=comb(8,n_alpha)*comb(8,n_beta)
    if expected>max_determinants:
        raise ValueError("CI expansion exceeds explicit determinant budget")
    states=sector(8,n_alpha,n_beta)
    amplitudes,_=trial_from_checkpoint(checkpoint,states,8,n_alpha,n_beta)
    if cutoff<0:raise ValueError("negative cutoff")
    indices=np.flatnonzero(abs(amplitudes)>cutoff)
    # iPie uses the leading determinant as its reference and the first N
    # determinants for its mean-field density. Sort by decreasing weight,
    # retaining each coefficient and its occupation indices together.
    indices=indices[np.argsort(-abs(amplitudes[indices]),kind="stable")]
    if indices.size==0:raise ValueError("cutoff removes all states")
    coefficients=amplitudes[indices].astype(np.complex128)
    coefficients/=np.linalg.norm(coefficients)
    occupancies_alpha=[]
    occupancies_beta=[]
    for pos in indices:
        s=states[int(pos)]
        occupancies_alpha.append([i for i in range(8) if s&(1<<i)])
        occupancies_beta.append([i for i in range(8) if s&(1<<(8+i))])
    occ_a=np.asarray(occupancies_alpha,dtype=np.int32).reshape(-1,n_alpha)
    occ_b=np.asarray(occupancies_beta,dtype=np.int32).reshape(-1,n_beta)
    return coefficients,occ_a,occ_b

def make_ipie_trial(checkpoint,num_elec,nbasis,cutoff=0.):
    from ipie.trial_wavefunction.particle_hole import ParticleHole
    ci,occ_a,occ_b=export_particle_hole(checkpoint,nbasis,
                                        int(num_elec[0]),int(num_elec[1]),cutoff)
    return ParticleHole((ci,occ_a,occ_b),tuple(num_elec),nbasis,
                        num_dets_for_trial=-1,
                        num_dets_for_props=min(100,len(ci)))

def metadata(checkpoint,num_elec,cutoff=0.):
    ci,occ_a,occ_b=export_particle_hole(checkpoint,8,*num_elec,cutoff)
    return {"scope":"finite full CI NQS -> iPie ParticleHole exact expansion",
            "checkpoint_sha256":hashlib.sha256(Path(checkpoint).read_bytes()).hexdigest(),
            "n_determinants":int(len(ci)),
            "sum_abs_coefficients_squared":float(np.vdot(ci,ci).real),
            "alpha_occupation_shape":list(occ_a.shape),
            "beta_occupation_shape":list(occ_b.shape),
            "source_original_IonQ_weights":False,
            "scaling":"exponential in active orbitals"}
