#!/usr/bin/env python3
"""Source-conditioned production molecular phaseless AFQMC via PySCF + ipie.

Method attribution:
  Zhao et al., Phys Rev Research 8, 033061 (2026), arXiv:2506.22408
  Provazza et al., arXiv:2611.08129 (2026)
  ipie developers (see https://ipie.readthedocs.io/en/latest/python_api.html)
No IonQ data/circuit/geometry is bundled or inferred. This is a classical
single-determinant reference unless a separate documented NQS trial is supplied.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import time

def run(config_path):
    source=Path(config_path).resolve()
    configuration=json.loads(source.read_text())
    for key in ("atoms","basis","charge","spin","unit","walkers","blocks",
                "steps_per_block","time_step","seed"):
        if key not in configuration:raise ValueError("missing required "+key)
    if not configuration.get("source_url"):
        raise ValueError("Molecular geometry requires explicit source_url")
    if not configuration.get("source_kind"):
        raise ValueError("Molecular geometry requires source_kind (e.g. original/independent)")
    if configuration["unit"] not in ("Angstrom","Bohr"):
        raise ValueError("unit must be Angstrom or Bohr")
    if not isinstance(configuration["atoms"],list) or not configuration["atoms"]:
        raise ValueError("atoms must be non-empty list")
    for entry in configuration["atoms"]:
        if len(entry)!=4:raise ValueError("atom is [element,x,y,z]")
    import numpy as np
    from pyscf import gto,scf
    from ipie.qmc.afqmc import AFQMC
    from ipie.trial_wavefunction.single_det import SingleDet
    from ipie.utils.from_pyscf import (
        generate_hamiltonian,generate_wavefunction_from_mo_coeff)
    mol=gto.M(atom=[(a[0],tuple(map(float,a[1:])))
                    for a in configuration["atoms"]],
              basis=configuration["basis"],
              charge=int(configuration["charge"]),
              spin=int(configuration["spin"]),
              unit=configuration["unit"],verbose=0)
    # Mean-field baseline, not a replacement for upCCD or the trained NQS.
    mf=scf.RHF(mol) if mol.spin==0 else scf.UHF(mol)
    mf.conv_tol=1e-10
    mf.max_cycle=200
    e_scf=mf.kernel()
    if not mf.converged:
        raise RuntimeError("SCF failed to converge; AFQMC not launched")
    coeff=mf.mo_coeff
    if isinstance(coeff,(tuple,list)):
        # Source documented UHF route: the selected orbital basis must be
        # common to both spins. Use a restricted open-shell reference here
        # rather than silently supplying incompatible UHF orbital frames.
        raise ValueError("Open-shell UHF requires explicit common-basis transformation")
    ham=generate_hamiltonian(mol,coeff,mf.get_hcore(),coeff)
    orbitals=generate_wavefunction_from_mo_coeff(coeff,mf.mo_occ,coeff,mol.nelec)
    if isinstance(orbitals,(tuple,list)):
        trial_coeff=np.hstack(orbitals)
    else:
        trial_coeff=np.hstack([orbitals,orbitals])
    trial=SingleDet(trial_coeff,mol.nelec,coeff.shape[-1])
    trial.compute_trial_energy=True
    trial.build()
    trial.half_rotate(ham)
    afqmc=AFQMC.build(mol.nelec,ham,trial,
       num_walkers=int(configuration["walkers"]),
       num_steps_per_block=int(configuration["steps_per_block"]),
       num_blocks=int(configuration["blocks"]),
       timestep=float(configuration["time_step"]),
       seed=int(configuration["seed"]),
       stabilize_freq=int(configuration.get("stabilize_freq",5)),
       pop_control_freq=int(configuration.get("pop_control_freq",5)),
       num_eq_blocks=int(configuration.get("equilibration_blocks",2)))
    output=source.with_suffix(".afqmc.h5")
    start=time.perf_counter()
    afqmc.run(estimator_filename=str(output))
    elapsed=time.perf_counter()-start
    afqmc.finalise(verbose=True)
    result={
      "scope":"PySCF + ipie classical determinant-trial molecular phaseless AFQMC",
      "original_IonQ_NQS_trial":False,
      "source_geometry":configuration["source_url"],
      "source_kind":configuration["source_kind"],
      "configuration_sha256":hashlib.sha256(source.read_bytes()).hexdigest(),
      "number_of_atoms":len(configuration["atoms"]),
      "electron_numbers":list(mol.nelec),
      "mean_field_hartree":float(e_scf),
      "trial_energy_hartree":float(np.real(trial.energy)),
      "runtime_seconds":elapsed,
      "estimator_hdf5":str(output),
      "note":"Reblock and report burn-in, timestep/walker/population convergence before quoting physical energy."}
    receipt=source.with_suffix(".afqmc.receipt.json")
    receipt.write_text(json.dumps(result,indent=2))
    return result

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("config",help="JSON with source-identified geometry and run settings")
    args=p.parse_args()
    print(json.dumps(run(args.config),indent=2))
