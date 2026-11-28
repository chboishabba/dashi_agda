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
    "check_engineered_gravity_l4_budget.py",
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
