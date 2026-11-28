"""Local fail-closed engineered-gravity symbolic acceptance runner.

Run on the PR checkout; no CI, no physical or native proof promotion.
"""
import argparse
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

CORE=(
    "check_engineered_gravity_proof_dag.py",
    "test_engineered_gravity_proof_dag.py",
    "check_engineered_gravity_coarse_to_fine.py",
    "check_engineered_gravity_endpoint_bidi.py",
    "check_engineered_gravity_receiver_inverse.py",
    "check_engineered_gravity_source_receiver_inverse.py",
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
    "check_tov_moving_second_shape.py",
    "check_tov_two_face_canonical_second.py",
    "check_tov_second_israel_shape.py",
    "check_tov_second_order_junction_inverse.py",
    "check_tov_moving_mass_constraint_weld.py",
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
    "check_tov_conformal_monopole_inverse.py",
    "check_tov_polar_conformal_trial.py",
    "check_tov_polar_coupled_trial.py",
    "check_tov_polar_projection_normalization.py",
    "check_tov_polar_ritz_search.py",
    "check_tov_polar_localization_sweep.py",
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
    p.add_argument("--work",type=Path,default=Path(".local-engineered-gravity"))
    p.add_argument("--resume",action="store_true")
    p.add_argument("--only",action="append",default=[])
    args=p.parse_args()
    if args.timeout<=0: raise ValueError("positive timeout required")
    root=Path(__file__).resolve().parent
    work=args.work.resolve(); work.mkdir(parents=True,exist_ok=True)
    ledger=work/"ledger.json"
    names=CORE+(DONORS if args.donors else ())
    if args.only:
        unknown=set(args.only)-set(names)
        if unknown: raise SystemExit("unknown checks: "+str(sorted(unknown)))
        names=tuple(n for n in names if n in args.only)
    # Pin all tracked checkout bytes via git status + tree identity;
    # refuse resume across dirty or changed checkouts.
    repo=root.parent
    def git(*cmd):
        return subprocess.check_output(["git",*cmd],cwd=repo,text=True).strip()
    identity={"head":git("rev-parse","HEAD"),"dirty":git("status","--porcelain","--untracked-files=no"),"python":sys.version,"timeout":args.timeout}
    if args.resume and identity["dirty"]: raise SystemExit("resume requires clean tracked checkout")
    old=json.loads(ledger.read_text()) if args.resume and ledger.exists() else {}
    if old and old.get("identity")!=identity: raise SystemExit("stale ledger identity; use new work directory")
    records=old.get("checks",{})
    def save():
        temp=ledger.with_suffix(".tmp")
        temp.write_text(json.dumps({"identity":identity,"checks":records,"scope":"symbolic/finite only; physical/native open"},indent=2,sort_keys=True))
        temp.replace(ledger)
    failures=[]
    for name in names:
        path=root/name; digest=hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None
        log=work/(name+".log")
        prev=records.get(name,{})
        if args.resume and digest and prev.get("sha256")==digest and prev.get("status")=="PASS" and log.is_file() and hashlib.sha256(log.read_bytes()).hexdigest()==prev.get("log_sha256"):
            print(name,"RESUMED PASS",flush=True);continue
        rec={"sha256":digest,"status":"BLOCKED" if digest is None else "RUNNING"}
        records[name]=rec;save()
        if digest is not None:
            with log.open("w") as out:
                try:
                    result=subprocess.run([sys.executable,str(path)],cwd=root,stdout=out,stderr=subprocess.STDOUT,timeout=args.timeout,env={**os.environ,"OPENBLAS_NUM_THREADS":"1","PYTHONDONTWRITEBYTECODE":"1"})
                    rec.update(status="PASS" if result.returncode==0 else "FAIL",exit_code=result.returncode)
                except subprocess.TimeoutExpired: rec.update(status="TIMEOUT")
                except OSError as exc: rec.update(status="BLOCKED",reason=str(exc))
            rec["log_sha256"]=hashlib.sha256(log.read_bytes()).hexdigest()
        save();print(name,rec["status"],flush=True)
        if rec["status"]!="PASS":failures.append(name)
    if failures: raise SystemExit("FAIL: "+", ".join(failures))
    print("PASS selected symbolic diagnostics; NOT physical or native certification")
if __name__=="__main__": main()
