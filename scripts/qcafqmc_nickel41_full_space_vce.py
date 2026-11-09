#!/usr/bin/env python3
"""Independent full-orbital nickel AFQMC with an active-space neural trial.

Source: Zhao et al., arXiv:2506.22408 §II.7, Eq. (30):
    |trial> = |occupied core> ⊗ |NQS active> ⊗ |virtual vacuum>.
The *propagator* uses the full molecular STO-3G Hamiltonian, NOT the core-
contracted CASCI Hamiltonian; this distinction is essential to recover
correlation outside the eight-orbital NQS active space.

Uses PySCF + ipie production modified-Cholesky/in-memory machinery.
This is an INDEPENDENT numerical approximation to the published VCE
workflow, not a reproduction of the author's exact orbital basis, hardware
weights, QPU noise mitigation or full-space overlap-acceleration algorithm.

Require explicit source identity, orbital-frame check and computational
budget. Default is dry-run metadata inspection; --execute launches expensive
full-molecule SCF/Cholesky/AFQMC only after validation.
"""
import argparse
import hashlib
import json
from pathlib import Path

from qcafqmc_nickel41_integrals import (GEOMETRY_DIR, SOURCE, read_xyz,
                                        geometry_receipts)

def validate(config_path,checkpoint=None):
    config_path=Path(config_path).resolve()
    config=json.loads(config_path.read_text())
    required=("geometry","basis","charge","spin","active_orbitals_zero_based",
              "electronic_state_source","orbital_selection_source")
    absent=sorted(set(required)-set(config))
    if absent:raise ValueError("missing source fields: "+str(absent))
    name=config["geometry"]
    if name not in ("B","BC","C"):raise ValueError("invalid source geometry")
    if str(config["basis"]).lower()!="sto-3g":
        raise ValueError("nickel target basis must be STO-3G")
    if not config["electronic_state_source"] or not config["orbital_selection_source"]:
        raise ValueError("unattributed physical electron state or orbital frame")
    order=config["active_orbitals_zero_based"]
    if len(order)!=8 or len(set(order))!=8 or any(
        type(i)!=int or i<0 for i in order):
        raise ValueError("eight distinct zero-based active orbitals required")
    if checkpoint:
        checkpoint=Path(checkpoint).resolve()
        if not checkpoint.is_file():raise ValueError("no neural checkpoint")
    path=GEOMETRY_DIR/(name+".xyz")
    atoms=read_xyz(path)
    receipt=geometry_receipts()[name]
    return config,atoms,{
        "scope":"independent full-space nickel QC-AFQMC with source-identified trial",
        "source_geometry":SOURCE,
        "structure":name,
        "geometry_sha256":receipt["sha256"],
        "input_configuration_sha256":hashlib.sha256(config_path.read_bytes()).hexdigest(),
        "charge":int(config["charge"]),"spin":int(config["spin"]),
        "electronic_state_source":config["electronic_state_source"],
        "orbital_source":config["orbital_selection_source"],
        "active_mo_indices_original_zero_based":order,
        "n_atoms":len(atoms),
        "checkpoint_sha256":hashlib.sha256(checkpoint.read_bytes()).hexdigest()
            if checkpoint else None,
        "author_orbital_frame_verified":bool(config.get("author_orbital_frame_verified",False)),
        "original_ionq_replication":False,
        "full_space_propagator":True,
        "VCE_trial_core_active_virtual_embedding":True}

def run(config_path,checkpoint=None,execute=False,max_basis=220,
        walkers=1280,blocks=300,steps_per_block=20,discard_blocks=50,
        dt=.005,seed=20261109):
    import numpy as np
    config,atoms,receipt=validate(config_path,checkpoint)
    if not (0<=discard_blocks<blocks and walkers>=1 and blocks>=1
            and steps_per_block>=1 and dt>0):
        raise ValueError("invalid AFQMC simulation settings")
    receipt.update({"walkers_per_rank":walkers,"measurement_blocks":blocks,
                    "steps_per_block":steps_per_block,"time_step":dt,
                    "discard_first_measured_blocks":discard_blocks,
                    "retained_blocks":blocks-discard_blocks,"seed":seed,
                    "executed":False})
    if not execute:return receipt
    if checkpoint and not config.get("same_PySCF_MO_frame_verified",False):
        raise ValueError("refuse a neural trial in an unverified orbital frame")

    from pyscf import gto,scf,mcscf
    from ipie.utils.from_pyscf import generate_hamiltonian
    from ipie.trial_wavefunction.single_det import SingleDet
    from ipie.trial_wavefunction.particle_hole import ParticleHole
    from ipie.qmc.afqmc import AFQMC
    from qcafqmc_nqs_ipie_particle_hole import export_particle_hole

    mol=gto.M(atom=atoms,basis="sto-3g",charge=int(config["charge"]),
              spin=int(config["spin"]),unit="Angstrom",verbose=0)
    if mol.spin!=0:raise ValueError("selected RHF implementation requires a singlet")
    nmo=mol.nao_nr()
    if nmo>max_basis:
        raise ValueError(f"full molecular basis has {nmo} functions; cap is {max_basis}")
    if mol.nelectron<8 or (mol.nelectron-8)%2:
        raise ValueError("inconsistent 8e8o active space and frozen occupied core")
    ncore=(mol.nelectron-8)//2
    indices=config["active_orbitals_zero_based"]
    if max(indices)>=nmo:raise ValueError("active orbital exceeds basis")
    mf=scf.RHF(mol)
    mf.conv_tol=float(config.get("scf_tolerance",1.e-9))
    energy=mf.kernel()
    if not mf.converged:raise RuntimeError("RHF did not converge")
    from qcafqmc_nickel41_integrals import PUBLISHED_RHF_HARTREE
    source_delta=float(energy-PUBLISHED_RHF_HARTREE[config["geometry"]])
    if abs(source_delta)>float(config.get("max_RHF_source_discrepancy_hartree",0.05)):
        raise ValueError("RHF does not match the original nickel Table 2 benchmark; stop before costly AFQMC")
    cas=mcscf.CASCI(mf,8,8)
    ordered=mcscf.sort_mo(cas,[x+1 for x in indices],base=1)
    assert ordered.shape==(nmo,nmo)
    import io
    buffer=io.BytesIO()
    np.save(buffer,np.asarray(ordered,dtype="<f8"))
    selected_mo_sha256=hashlib.sha256(buffer.getvalue()).hexdigest()
    if checkpoint:
        import torch
        metadata=torch.load(checkpoint,map_location="cpu",weights_only=True)
        if (metadata.get("orbital_frame_sha256")!=selected_mo_sha256
                or metadata.get("geometry_sha256")!=receipt["geometry_sha256"]):
            raise ValueError("NQS checkpoint does not belong to this full-space MO frame and source geometry")
    # Important: no CASCI active-orbital contraction here: the ipie
    # Hamiltonian still includes every virtual and occupied orbital.
    ham=generate_hamiltonian(mol,ordered,mf.get_hcore(),ordered)
    if ham.nbasis!=nmo:raise RuntimeError("Hamiltonian lost full basis")
    nalpha=nbeta=mol.nelectron//2
    if checkpoint:
        ci,alpha,beta=export_particle_hole(checkpoint,8,4,4,cutoff=0.)
        core=np.tile(np.arange(ncore,dtype=np.int32),(len(ci),1))
        oa=np.hstack((core,alpha+ncore))
        ob=np.hstack((core,beta+ncore))
        trial=ParticleHole((ci,oa,ob),(nalpha,nbeta),nmo,
                           num_dets_for_trial=-1,
                           num_dets_for_props=len(ci))
        kind="paired_NQS_full_space_trial"
    else:
        orb=np.eye(nmo,dtype=np.complex128)[:,:nalpha]
        trial=SingleDet(np.hstack((orb,orb)),(nalpha,nbeta),nmo)
        kind="source_RHF_full_space_trial"
    trial.compute_trial_energy=True
    trial.build()
    trial.half_rotate(ham)
    afqmc=AFQMC.build((nalpha,nbeta),ham,trial,
                      num_walkers=walkers,num_blocks=blocks,
                      num_steps_per_block=steps_per_block,timestep=dt,
                      seed=seed,stabilize_freq=5,pop_control_freq=5,
                      num_eq_blocks=0)
    out=Path(config_path).resolve().parent/(receipt["structure"]+"_"+kind+".h5")
    afqmc.run(estimator_filename=str(out))
    afqmc.finalise(verbose=True)
    if not out.is_file():raise RuntimeError("missing ipie energy estimates")
    receipt.update({"executed":True,"full_basis_functions":nmo,
                    "ncore_doubly_occupied_trial":ncore,
                    "active_MO_columns_sorted":[ncore,ncore+7],
                    "selected_mo_sha256":selected_mo_sha256,
                    "SCF_energy_hartree":float(energy),
                    "source_RHF_hartree":PUBLISHED_RHF_HARTREE[config["geometry"]],
                    "RHF_minus_source_hartree":source_delta,
                    "trial_energy_hartree":float(np.real(trial.energy)),
                    "trial_type":kind,"estimates_hdf5":str(out),
                    "original_ionq_trial":False})
    output=out.with_suffix(".receipt.json")
    output.write_text(json.dumps(receipt,indent=2)+"\n")
    return receipt

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("nickel_config")
    p.add_argument("--checkpoint")
    p.add_argument("--execute",action="store_true")
    p.add_argument("--max-basis",type=int,default=220)
    p.add_argument("--walkers",type=int,default=1280)
    p.add_argument("--blocks",type=int,default=300)
    args=p.parse_args()
    print(json.dumps(run(args.nickel_config,args.checkpoint,
                         args.execute,args.max_basis,args.walkers,args.blocks),indent=2))
