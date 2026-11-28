"""Local fail-closed engineered-gravity symbolic acceptance runner.

Run on the PR checkout; no CI, no physical or native proof promotion.
"""
import argparse
import subprocess
import sys
from pathlib import Path

CORE=(
    "check_engineered_gravity_coarse_to_fine.py",
    "check_engineered_gravity_endpoint_bidi.py",
    "check_engineered_gravity_coupled_radion_material.py",
    "check_engineered_gravity_same_action_geometry.py",
    "check_engineered_gravity_derivative_action.py",
    "check_engineered_gravity_finite_interface.py",
    "check_engineered_gravity_l3_action_boundary.py",
    "check_engineered_gravity_l3_source_geometry.py",
    "check_engineered_gravity_finite_source_families.py",
    "check_engineered_gravity_finite_admissibility.py",
    "check_engineered_gravity_shell_dynamics.py",
    "check_engineered_gravity_general_shell_hybrid.py",
    "check_engineered_gravity_localized_source_action.py",
    "check_engineered_gravity_alternative_mechanisms.py",
    "check_engineered_gravity_static_tensor_constraints.py",
    "check_engineered_gravity_finite_response_history.py",
    "check_engineered_gravity_source_driven.py",
    "check_engineered_gravity_action_contrast.py",
    "check_engineered_gravity_reciprocal_action_shell.py",
    "check_engineered_gravity_smooth_order.py",
    "check_engineered_gravity_axisymmetric_order.py",
    "check_engineered_gravity_cubic_receiver.py",
    "check_engineered_gravity_hopf_receiver.py",
    "check_engineered_gravity_same_source_observers.py",
    "check_engineered_gravity_hopf_full_receiver.py",
    "check_engineered_gravity_hopf_time_receiver.py",
    "check_engineered_gravity_hopf_axial_trajectory.py",
    "check_engineered_gravity_hopf_fourth_jet.py",
    "check_engineered_gravity_quartic_receiver.py",
    "check_engineered_gravity_g3_analytic_radius.py",
    "check_engineered_gravity_g3_split_majorant.py",
    "check_engineered_gravity_g3_weighted_majorant.py",
    "check_engineered_gravity_g3_evolve.py",
    "check_engineered_gravity_g3_domain.py",
    "check_engineered_gravity_g3_harmonic.py",
    "check_engineered_gravity_g3_harmonic_receiver.py",
    "check_engineered_gravity_nonlinear_shell.py",
    "check_engineered_gravity_shell_ward_hessian.py",
    "check_engineered_gravity_shell_compliance.py",
    "check_engineered_gravity_same_endpoint_active.py",
    "check_engineered_gravity_exact_tov.py",
    "check_engineered_gravity_tov_material.py",
    "check_engineered_gravity_l4_budget.py",
    "check_tov_moving_interface.py",
    "check_tov_constrained_mass_hessian.py",
    "check_tov_causal_constitutive_repair.py",
    "check_tov_radial_dynamics.py",
    "check_tov_graph_trace.py",
    "check_tov_causal_tube_and_junction.py",
    "check_tov_axial_rotation_harmonics.py",
    "check_tov_axial_frame_dragging.py",
    "check_tov_covariant_matter_hessian.py",
    "check_tov_einstein_harmonic_jets.py",
    "check_tov_harmonic_gauge_boundary.py",
    "check_tov_master_trace_reconstruction.py",
    "check_tov_vacuum_master_oracle.py",
    "check_tov_axial_constraint_inverse.py",
    "check_tov_axial_master_flux.py",
    "check_tov_polar_hamiltonian.py",
    "check_tov_polar_master_flux.py",
    "check_tov_polar_york.py",
    "check_tov_global_york_axial_shear.py",
    "check_tov_axial_spatial_action.py",
    "check_tov_conformal_mass_second_variation.py",
)
DONORS=(
    "check_kk_radion_reduced_action.py",
    "check_kk_radion_spherical_match.py",
    "check_kk_coupled_radion_magnetic_5d.py",
    "check_kk_maxwell_first_integral_radion_source.py",
    "check_kk_sc_radion_braking_reduction.py",
    "check_kk_rebco_vortex_screening_maxcut.py",
    "check_kk_chameleon_material_contrast.py",
    "check_kk_rectified_leggett_rqu_ghz.py",
    "check_kk_source_matching_gate.py",
    "check_kk_same_action_stress.py",
    "check_kk_casimir_bidi_consumer.py",
    "check_kk_jordan_sourced_sphere.py",
    "check_sc_coherent_braking_same_source_dynamics.py",
)
def main():
    p=argparse.ArgumentParser()
    p.add_argument("--donors",action="store_true")
    p.add_argument("--timeout",type=int,default=90)
    args=p.parse_args()
    if args.timeout<=0: raise ValueError("positive timeout required")
    root=Path(__file__).resolve().parent
    failures=[]
    for name in CORE+(DONORS if args.donors else ()):
        try:
            result=subprocess.run([sys.executable,str(root/name)],cwd=root,
                                  capture_output=True,text=True,timeout=args.timeout)
            print(name,result.returncode,result.stdout,result.stderr,flush=True)
            if result.returncode: failures.append(name)
        except subprocess.TimeoutExpired:
            failures.append(name); print(name,"TIMEOUT",flush=True)
    if failures: raise SystemExit("FAIL: "+", ".join(failures))
    print("PASS selected symbolic diagnostics; NOT physical or native certification")
if __name__=="__main__": main()
