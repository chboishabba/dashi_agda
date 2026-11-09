#!/usr/bin/env python3
"""Local-only QC-AFQMC source/algorithm acceptance harness.

No GitHub CI, QPU, PySCF or ipie required for --source. Executes all
source-level references, exact printed numerical relations, and basic
finite VCE overlap negative controls. It NEVER marks original nickel
AFQMC energies as obtained.
"""
import argparse
import compileall
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent

def run(include_torch=False):
    checked=[]
    for path in sorted(HERE.glob("qcafqmc_*.py")):
        # Compile from the actual local file bytes rather than relying
        # on stale Python bytecode or previous source snippets.
        compile(path.read_bytes(),str(path),"exec")
        checked.append(path.name)
    from qcafqmc_nickel41_source_check import verify as verify_nickel_source
    from qcafqmc_nickel_published_targets import verify as verify_targets
    from qcafqmc_nickel_cost_source_reconciliation import audit as cost_audit
    from qcafqmc_vce_full_space_overlap_check import validate as validate_vce
    from qcafqmc_mixed_energy_error_certificate import self_test as check_ratio
    from qcafqmc_autocorrelation_reblocking import self_test as check_autocorr
    from qcafqmc_nickel_doci_trial import self_test as check_doci
    from qcafqmc_existing_hartree_fock_reuse import verify_hf_reuse
    from qcafqmc_molecular_scf_certificate import self_test as check_scf
    source=verify_nickel_source()
    targets=verify_targets()
    costs=cost_audit()
    vce=validate_vce()
    ratio=check_ratio()
    autocorr=check_autocorr()
    doci=check_doci()
    hf_reuse=verify_hf_reuse()
    scf_certificate=check_scf()
    if not scf_certificate["wrong_orbital_order_rejected"]:
        raise AssertionError("molecular SCF wrong-frame negative control")
    if not hf_reuse["one_orbital_HF_and_exact_FCI_same_Hamiltonian"]:
        raise AssertionError("existing helium Hartree/RHF equivalence not preserved")
    if not (autocorr["passed"] and doci["small_hubbard_projected_matrix_matches_FCI"]):
        raise AssertionError("autocorrelation or DOCI projection regression")
    if costs["retained_measured_blocks"]!=250:
        raise AssertionError("nickel 300 measured blocks with 50 discarded")
    if not vce["passed"] or not ratio["near_node_rejected"]:
        raise AssertionError("VCE or overlap near-node negative control")
    if include_torch:
        from qcafqmc_paired_nqs_check import main as test_paired
        from qcafqmc_nqs_ipie_particle_hole_check import test_same_sector_export
        test_paired()
        test_same_sector_export()
    return {
      "scope":"local source and small-system acceptance only",
      "all_qcafqmc_python_files_compiled":len(checked),
      "nickel_source_composition_passed":source["passed"],
      "published_energy_references_checked":targets["rounded_absolute_energy_deltas_checked"],
      "published_cost_saving_fraction":costs["estimated_saving_fraction"],
      "VCE_block_factorization_error":vce["block_separated_overlap_error"],
      "VCE_mixed_core_negative_control":vce["naive_active_overlap_failure_under_core_mixing"],
      "mixed_energy_near_node_rejected":ratio["near_node_rejected"],
      "torch_70_state_tests_executed":include_torch,
      "autocorrelation_AR1_negative_control_passed":autocorr["passed"],
      "autocorrelation_blocking_to_naive_SE_ratio":(
          autocorr["B_blocked_SE"]/autocorr["B_naive_IID_SE"]),
      "existing_Hartree_one_orbital_RHF_reused":hf_reuse["one_orbital_HF_and_exact_FCI_same_Hamiltonian"],
      "new_HF_solver_claimed":False,
      "molecular_SCF_wrong_MO_frame_rejected":scf_certificate["wrong_orbital_order_rejected"],
      "DOCI_projected_Hubbard_matches_exact_FCI_subblock":doci["small_hubbard_projected_matrix_matches_FCI"],
      "DOCI_vs_FCI_seniority_gap_positive":doci["seniority_zero_approximation_gap_positive"],
      "PySCF_ipie_nickel_runs_executed":False,
      "original_ionq_replication":False,
      "checked_files":checked
    }
if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--with-torch",action="store_true",
                   help="also run synthetic paired-state neural/CI tests")
    a=p.parse_args()
    print(json.dumps(run(a.with_torch),indent=2))
