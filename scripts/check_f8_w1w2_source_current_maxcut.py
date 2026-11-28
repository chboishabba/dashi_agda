"""Reconciled F8 W1/W2 local acceptance: exact wall source/current/Schur checks,
with separate opt-in original finite-history gate. Never invokes CI.
No automatic promotion from symbolic algebra to coupled physical solution.
"""
import argparse
import os
import subprocess
import sys
from pathlib import Path

SCRIPTS=(
    "check_f8_actual_gn_current.py",
    "check_f8_full_gn_fourier_current.py",
    "check_f8_gn_current_budget.py",
    "check_f8_current_israel_reciprocal_weld.py",
    "check_f8_differentiated_gn_energy.py",
    "check_f8_gn_coefficient_enclosure.py",
    "check_f8_two_level_source_energy.py",
    "check_f8_gn_commutator_graph_reduction.py",
    "check_f8_gn_graph_majorant.py",
    "check_f8_gn_graph_energy_growth.py",
    "check_f8_two_level_israel_trace_closure.py",
    "check_f8_israel_trace_source_schur.py",
    "check_f8_ward_timejet_receipt.py",
    "check_f8_timejet_stencil_certificate.py",
    "check_f8_characteristic_jet_reverse.py",
    "check_f8_characteristic_jet_caps.py",
    "check_f8_characteristic_to_ward_weld.py",
    "check_f8_original_wall_normal_jet.py",
    "check_f8_normal_graph_hierarchy.py",
    "check_f8_characteristic_pde_weld.py",
    "check_f8_normal_graph_trace_socket.py",
    "check_f8_normal_graph_energy_hierarchy.py",
    "check_f8_wall_elliptic_jet_weld.py",
    "check_f8_wall_elliptic_jet_caps.py",
    "check_f8_normal_jet_cycle_audit.py",
    "check_f8_time6_neumann_energy_bridge.py",
    "check_f8_time6_two_boundary.py",
    "check_f8_time6_corrected_energy.py",
    "check_f8_outgoing_triangular_weld.py",
    "check_f8_outgoing_flux_caps.py",
    "check_f8_characteristic_conormal_time6.py",
    "check_f8_time6_initial_compatibility.py",
    "check_f8_original_pulse_derivative_bounds.py",
    "check_f8_full_ward_jet_majorant.py",
    "check_f8_original_pulse_jet_receipt.py",
    "check_f8_retarded_controller_jet_enclosure.py",
    "check_f8_original_source_jet_closure.py",
    "check_f8_gauss_israel_energy_weld.py",
    "check_f8_scalar_density_momentum_schur.py",
    "check_f8_material_momentum_frame_weld.py",
    "check_f8_scalar_frequency_schur_bridge.py",
    "check_f8_scalar_master_flux_weld.py",
    "check_f8_full_band_ward_attachment.py",
)

def run(history=False,original_jets=False,original_normal=False,seconds=30):
    root=Path(__file__).resolve().parent
    env=dict(os.environ,OPENBLAS_NUM_THREADS="1",OMP_NUM_THREADS="1")
    tasks=[(name,()) for name in SCRIPTS]
    if history:tasks.append(("check_f8_w1w2_integrated_receipt.py",()))
    if original_jets:tasks.append(("check_f8_ward_timejet_receipt.py",("--original",)))
    if original_normal:tasks.append(("check_f8_original_wall_normal_jet.py",("--original",)))
    for name,extra in tasks:
        path=root/name
        if not path.is_file():raise FileNotFoundError(path)
        result=subprocess.run((sys.executable,str(path),*extra),cwd=root,env=env,
                              capture_output=True,text=True,
                              timeout=90 if extra or name.endswith("integrated_receipt.py") else seconds)
        if result.returncode:
            raise RuntimeError(f"{name} FAILED rc={result.returncode}\n{result.stdout}\n{result.stderr}")
        print(f"PASS {name}: {result.stdout.strip()[:220]}",flush=True)
    print("EXACT ALGEBRA ACCEPTED; original history="+("EXECUTED" if history else "NOT EXECUTED"))
    print("Original full Ward time-jets="+("EXECUTED, UNCERTIFIED" if original_jets else "NOT EXECUTED"))
    print("Original normal second-jet="+("EXECUTED, UNCERTIFIED" if original_normal else "NOT EXECUTED"))
    print("Full continuum Einstein-Israel physical energy and receiver remain OPEN")

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--history",action="store_true",help="run original finite history, 90s local cap")
    p.add_argument("--original-jets",action="store_true",help="run actual full-band Ward time-jets, 90s local cap")
    p.add_argument("--original-normal",action="store_true",help="run original characteristic 64/128 cell normal-jet diagnostic")
    p.add_argument("--seconds",type=int,default=30,help="per exact script timeout")
    args=p.parse_args()
    run(args.history,args.original_jets,args.original_normal,args.seconds)
