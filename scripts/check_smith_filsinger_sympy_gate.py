#!/usr/bin/env python3
"""D1 fail-closed exact SymPy gate for F13/F15.

Requires a real Agda compiler run for D1_KERN. SymPy is an independent
algebraic oracle, NOT an Agda parser, typechecker or kernel.
"""
from pathlib import Path
import json
import subprocess
import sys

ROOT=Path(__file__).resolve().parent.parent
SOURCE=ROOT/"DASHI/Physics/Motors"
REQUIRED={
    "SmithFilsingerCoerciveGreenRetardedWeldExact.agda":
      ("greenAtArrivalInheritsCoerciveBound","selectedPhysicalFrontDistanceBound"),
    "SmithFilsingerPeriodicGreenDelayReuseExact.agda":
      ("delayedPeriodicGreenSolvesMeanCorrectedLaplacian",),
    "SmithFilsingerSpaceTimePoyntingTelescopeExact.agda":
      ("spaceTimeExteriorEnergyBalance","partitionedSpaceTimeExteriorBudget"),
    "SmithFilsingerHundredfoldSourceFundingExact.agda":
      ("hundredfoldRequiresSourcedWork","hundredfoldNeedsBudget"),
    "SmithFilsingerLocalCausalADEReachExact.agda":
      ("ZeroPreserving","oneStepOutsideZero",
       "noSignalOutsideDynamicCone","seedReach",
       "noSignalOutsideInterleavedSourceCone","additiveZeroPreserving"),
    "SmithFilsingerLocalCayleyZeroWeldExact.agda":
      ("CertifiedCayley","sameCayleyFirstZero","sameCayleySecondZero",
       "sameCayleyZeroPreserving","guardedDistinctCayleyEdge",
       "diagonalCayleyZero","singleCayleyWithSourceNoSignalOutsideReach"),
    "SmithFilsingerLocalCayleyMidpointExact.agda":
      ("CertifiedHalfStep","halfStepInverseLaw",
       "sameFirstIsReduced","sameSecondIsReduced",
       "firstMidpointPolynomial","secondMidpointPolynomial",
       "sameCayleyFirstMidpoint","sameCayleySecondMidpoint"),
    "SmithFilsingerIndexedCayleyFaceWeldExact.agda":
      ("IndexedCayleyFace","indexedSourceIDExact","indexedTargetIDExact",
       "indexedGuardedSamePrimitive","indexedFaceFirstMidpoint",
       "indexedFaceSecondMidpoint","indexedFaceSourceCone",
       "MeshSelectedCayleyFace","selectedReallyOccurs",
       "meshSelectedFaceMidpointFirst","meshSelectedFaceMidpointSecond"),
}
TESTS=[str(ROOT/"scripts/test_smith_filsinger_layered_green_sympy.py"),
       str(ROOT/"scripts/test_smith_filsinger_tangential_maxwell_sympy.py"),
       str(ROOT/"scripts/test_smith_filsinger_radiation_green_sympy.py"),
       str(ROOT/"scripts/test_smith_filsinger_oblique_maxwell_sympy.py"),
       str(ROOT/"scripts/test_smith_filsinger_passive_radiation_sympy.py"),
       str(ROOT/"scripts/test_smith_filsinger_periodic_fourier_green_sympy.py"),
       str(ROOT/"scripts/test_smith_filsinger_lorentz_ade_sympy.py"),
       str(ROOT/"scripts/test_smith_filsinger_lorentz_maxwell_weld_sympy.py"),
       str(ROOT/"scripts/test_smith_filsinger_local_causal_ade_sympy.py"),
       str(ROOT/"scripts/test_smith_filsinger_cayley_coefficients_sympy.py"),
       str(ROOT/"scripts/test_smith_filsinger_cayley_midpoint_sympy.py"),
       str(ROOT/"scripts/test_smith_filsinger_indexed_cayley_face_sympy.py")]

def audit():
    errors=[]
    for name,tokens in REQUIRED.items():
        f=SOURCE/name
        if not f.exists():
            errors.append(f"missing original Agda source {name}")
            continue
        s=f.read_text(encoding="utf-8")
        for token in tokens:
            if token not in s:errors.append(f"{name}: missing {token}")
        if "{!!}" in s:errors.append(f"{name}: explicit Agda hole")
        for line in s.splitlines():
            if line.lstrip().startswith("postulate "):
                errors.append(f"{name}: explicit postulate")
    return errors

def main():
    errors=audit()
    status={"sympy_exact":"NOT_RUN","agda_kernel":"NOT_RUN",
            "physical_same_original_source":"UNVERIFIED",
            "physical_f13_dyadic":"OPEN","physical_f15_sustained_gain":"OPEN",
            "D1_kernel_gate":"OPEN","static_source_errors":errors}
    if errors:
        print(json.dumps(status,indent=2));return 1
    run=subprocess.run([sys.executable,"-m","pytest","-q",*TESTS],
                       cwd=str(ROOT),capture_output=True,text=True)
    status["sympy_exact"]="PASS" if run.returncode==0 else "FAIL"
    status["pytest_output"]=(run.stdout+"\n"+run.stderr).strip()[-1000:]
    # NEVER set the kernel flag on an independent SymPy result.
    print(json.dumps(status,indent=2))
    return run.returncode

if __name__=="__main__":
    raise SystemExit(main())
