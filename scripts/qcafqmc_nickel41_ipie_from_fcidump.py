#!/usr/bin/env python3
"""Same-source nickel CASCI FCIDUMP -> iPie phaseless AFQMC.

Runs either a single-determinant (reference) or an independent paired-NQS CI
trial against the *identical* source-locked (8e,8o) Hamiltonian file.

Uses ipie's documented fcidump_to_afqmc.py Cholesky converter, MPIHandler,
get_hamiltonian(), SingleDet/ParticleHole and AFQMC.build. This is an ACTIVE-
SPACE AFQMC baseline, NOT the paper's full-space virtual correlation energy
(VCE) propagation or a claim of original IonQ checkpoint replication.

Attribution: Zhao et al. arXiv:2506.22408; Provazza et al.
arXiv:2611.08129; ipie 0.7.1 user documentation.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import os
import sys
import importlib.util
import time

def source_digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def run(receipt_file,checkpoint=None,doci_npz=None,walkers=1280,blocks=300,steps_per_block=20,
        time_step=.005,eq_blocks=0,analysis_discard_blocks=50,seed=20261109,chol_threshold=1e-5):
    import numpy as np
    receipt_file=Path(receipt_file).resolve()
    receipt=json.loads(receipt_file.read_text())
    if receipt.get("scope")!="41-atom nickel source-geometry, RHF/STO-3G active (8e,8o)":
        raise ValueError("input is not the source-locked nickel CASCI receipt")
    fcidump=Path(receipt["integral_fcidump"]).resolve()
    if not fcidump.is_file() or source_digest(fcidump)!=receipt["integral_sha256"]:
        raise ValueError("molecular integral input missing or SHA256 changed")
    if (receipt.get("ncore") is None or
            receipt.get("active_orbital_indices_zero_based") is None):
        raise ValueError("missing inactive-core or orbital-frame certificate")
    if checkpoint and doci_npz:
        raise ValueError("choose either learned NQS or independent DOCI, not both")
    if min(walkers,blocks,steps_per_block)<1 or time_step<=0:
        raise ValueError("invalid AFQMC parameters")
    if not 0<=eq_blocks<blocks:
        raise ValueError("explicit equilibration blocks invalid")
    if not 0<=analysis_discard_blocks<blocks:
        raise ValueError("analysis discard blocks invalid")
    if blocks!=300 or steps_per_block!=20 or abs(time_step-.005)>1e-12:
        raise ValueError("this original-source protocol expects 300 blocks, 20 steps, dt=.005")

    # Production document route. No ad-hoc chemists'/physicists'
    # ERI transposition or Cholesky factorization is introduced here.
    converter=os.environ.get("IPIE_FCIDUMP_CONVERTER") or shutil.which("fcidump_to_afqmc.py")
    if not converter:
        spec=importlib.util.find_spec("ipie")
        if spec and spec.origin:
            package_root=Path(spec.origin).resolve().parent
            candidates=(package_root.parent/"tools"/"fcidump_to_afqmc.py",
                        package_root/"tools"/"fcidump_to_afqmc.py")
            converter=next((str(p) for p in candidates if p.is_file()),None)
    if not converter or not Path(converter).is_file():
        raise RuntimeError("pin ipie tools/fcidump_to_afqmc.py with IPIE_FCIDUMP_CONVERTER")
    out=receipt_file.parent/(receipt["structure"]+"_active_ipie.h5")
    command=([sys.executable,str(converter)] if str(converter).endswith(".py")
             else [str(converter)])
    subprocess.run(command+["-i",str(fcidump),"-o",str(out),
                    "-t",str(float(chol_threshold)),"-s","8"],check=True)
    if not out.is_file():raise RuntimeError("ipie Hamiltonian conversion produced no file")
    from ipie.utils.mpi import MPIHandler
    from ipie.hamiltonians.utils import get_hamiltonian
    from ipie.trial_wavefunction.single_det import SingleDet
    from ipie.qmc.afqmc import AFQMC
    handler=MPIHandler()
    ham=get_hamiltonian(str(out),handler.scomm,pack_chol=True,verbose=False)
    from qcafqmc_fcidump_cholesky_identity import check_ipie_hamiltonian
    cholesky_certificate=check_ipie_hamiltonian(
        str(fcidump),ham,threshold=float(chol_threshold)*5)
    nalpha=nbeta=4
    if ham.nbasis!=8:raise ValueError("expected eight-orbital CASCI Hamiltonian")
    if checkpoint:
        from qcafqmc_nqs_ipie_particle_hole import make_ipie_trial
        checkpoint=Path(checkpoint).resolve()
        if not checkpoint.is_file():raise ValueError("neural trial checkpoint absent")
        import torch
        metadata=torch.load(checkpoint,map_location="cpu",weights_only=True)
        if not receipt.get("selected_mo_sha256") or (
                metadata.get("orbital_frame_sha256")!=receipt["selected_mo_sha256"]
                or metadata.get("geometry_sha256")!=receipt["geometry_sha256"]):
            raise ValueError("neural checkpoint and CASCI selected orbital/geometry frame differ or are unverified")
        trial=make_ipie_trial(str(checkpoint),(4,4),8,cutoff=0.)
        trial_type="paired_NQS_full_CI"
    elif doci_npz:
        from ipie.trial_wavefunction.particle_hole import ParticleHole
        with np.load(doci_npz,allow_pickle=False) as z:
            if z["fcidump_sha256"].item()!=source_digest(fcidump):
                raise ValueError("DOCI FCIDUMP does not match nickel Hamiltonian")
            if z["orbital_frame_sha256"].item()!=receipt.get("selected_mo_sha256") or (
                    z["geometry_sha256"].item()!=receipt.get("geometry_sha256")):
                raise ValueError("DOCI source geometry/MO frame differs")
            coeffs=z["coefficients"].copy()
            occa=z["occ_alpha"].copy()
            occb=z["occ_beta"].copy()
        order=np.argsort(-np.abs(coeffs),kind="stable")
        trial=ParticleHole((coeffs[order],occa[order],occb[order]),
                            (4,4),8,num_dets_for_trial=-1,
                            num_dets_for_props=len(coeffs))
        trial_type="independent_DOCI"
    else:
        occupied=np.eye(8,dtype=np.complex128)[:,:4]
        trial=SingleDet(np.hstack((occupied,occupied)),(4,4),8)
        trial_type="HF_determinant_in_selected_MO_frame"
    trial.compute_trial_energy=True
    trial.build()
    trial.half_rotate(ham)
    afqmc=AFQMC.build((nalpha,nbeta),ham,trial,
         num_walkers=int(walkers),num_blocks=int(blocks),
         num_steps_per_block=int(steps_per_block),timestep=float(time_step),
         seed=int(seed),stabilize_freq=5,pop_control_freq=5,
         num_eq_blocks=int(eq_blocks))
    estimator=receipt_file.parent/(receipt["structure"]+"_"+trial_type+".h5")
    start=time.perf_counter()
    afqmc.run(estimator_filename=str(estimator))
    elapsed=time.perf_counter()-start
    afqmc.finalise(verbose=True)
    if not estimator.is_file():raise RuntimeError("missing AFQMC estimator output")
    output={"scope":"source-locked nickel (8e,8o) *active-space* ipie phaseless",
            "structure":receipt["structure"],"trial_type":trial_type,
            "integral_sha256":source_digest(fcidump),
            "ipie_hamiltonian_sha256":source_digest(out),
            "same_source_cholesky_certificate":cholesky_certificate,
            "trial_checkpoint_sha256":source_digest(checkpoint) if checkpoint else None,
            "DOCI_source_sha256":source_digest(doci_npz) if doci_npz else None,
            "geometry_sha256":receipt["geometry_sha256"],
            "charge_spin_source":receipt["charge_spin_source"],
            "orbital_selection_source":receipt["orbital_selection_source"],
            "orbital_frame_verified_original":receipt["original_ionq_orbital_frame_verified"],
            "trial_variational_energy_hartree":float(np.real(trial.energy)),
            "walkers":walkers,"blocks":blocks,"seed":seed,"explicit_equilibration_blocks":eq_blocks,
            "analysis_discard_blocks":analysis_discard_blocks,
            "analysis_retained_blocks":blocks-analysis_discard_blocks,
            "steps_per_block":steps_per_block,"time_step":time_step,
            "elapsed_seconds":elapsed,"estimator":str(estimator),
            "original_ionq_nickel_replication":False,
            "full_space_VCE_reproduced":False,
            "note":"Reblock independent estimates and test timestep/walker convergence before quoting energy"}
    out_receipt=receipt_file.parent/(receipt["structure"]+"_"+trial_type+".receipt.json")
    out_receipt.write_text(json.dumps(output,indent=2)+"\n")
    return output

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("nickel_casci_receipt")
    p.add_argument("--nqs-checkpoint")
    p.add_argument("--doci-npz")
    p.add_argument("--walkers",type=int,default=1280)
    p.add_argument("--blocks",type=int,default=300)
    p.add_argument("--seed",type=int,default=20261109)
    a=p.parse_args()
    print(json.dumps(run(a.nickel_casci_receipt,a.nqs_checkpoint,a.doci_npz,
                         a.walkers,a.blocks,seed=a.seed),indent=2))
