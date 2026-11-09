#!/usr/bin/env python3
"""Reuse existing DASHI atomic helium Hartree/RHF-equivalent producer.

The original repo already contains:
  scripts/atomic_helium_hartree_scf.py
  scripts/atomic_helium_hartree_convergence.py
and the associated Agda convergence receipt.

Restricted one-orbital two-electron Hartree is identical to RHF for the same
spatial orbital: E=2h11+(11|11), because the same-spin exchange cancels
self-interaction and the opposite-spin electron contributes one Coulomb J.

This verifies the *method reuse*, not a nickel HF run or a reusable set of
nickel Gaussian orbitals. PySCF remains the molecular integral producer.
"""
import json
import numpy as np
from qcafqmc_molecular_fcidump import fci_matrix

def verify_hf_reuse():
    from atomic_helium_hartree_convergence import (
        HF_LIMIT_HARTREE,PEKERIS_NONREL_GROUND_HARTREE)
    from atomic_helium_hartree_scf import (
        HARTREE_EV_2022_CODATA,NIST_HEI_IE_EV)
    h=np.array([[-1.2]])
    eri=np.array([[[[.8]]]])
    ecore=.3
    electronic=2*h[0,0]+eri[0,0,0,0]
    H,states=fci_matrix(h,eri,1,1,ecore)
    assert len(states)==1
    assert np.isclose(H[0,0],electronic+ecore,atol=1e-12)
    # Closed-shell Fock diagonal is h + 2J - K = h + J.
    one_particle_fock=h[0,0]+eri[0,0,0,0]
    hf_from_orbital=2*one_particle_fock-eri[0,0,0,0]+ecore
    assert np.isclose(hf_from_orbital,H[0,0],atol=1e-12)
    assert HF_LIMIT_HARTREE > PEKERIS_NONREL_GROUND_HARTREE
    return {
      "existing_hartree_source":"scripts/atomic_helium_hartree_scf.py",
      "existing_convergence_source":"scripts/atomic_helium_hartree_convergence.py",
      "atomic_method":"single-spatial-orbital closed-shell Hartree; RHF-equivalent",
      "one_orbital_HF_and_exact_FCI_same_Hamiltonian":True,
      "independent_one_orbital_energy_hartree":float(H[0,0]),
      "helium_published_HF_limit_hartree":HF_LIMIT_HARTREE,
      "helium_published_correlated_benchmark_hartree":PEKERIS_NONREL_GROUND_HARTREE,
      "HF_to_correlated_gap_hartree":HF_LIMIT_HARTREE-PEKERIS_NONREL_GROUND_HARTREE,
      "source_NIST_helium_IE_eV":NIST_HEI_IE_EV,
      "source_Hartree_to_eV":HARTREE_EV_2022_CODATA,
      "nickel_molecular_HF_executed_here":False,
      "new_Hartree_Fock_solver_claimed":False
    }
if __name__=="__main__":
    print(json.dumps(verify_hf_reuse(),indent=2))
