#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_ns_luo_physical_conditional_round17.sh

files=(
  DASHI/Physics/Common/GradedLocalCompatibilitySystemExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoShellGradedLocalCompatibilityExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoWeightedIntegratedAbsorptionSummationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCubicTransferStrongLimitInterfaceExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoIntegratedAbsorptionRound18Validation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "round eighteen contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

grep -q 'transportDefectTwice' DASHI/Physics/Common/GradedLocalCompatibilitySystemExact.agda
grep -q 'interactionProbesSeparate' DASHI/Physics/Closure/NSTriadKNLuoShellGradedLocalCompatibilityExact.agda
grep -q 'profileAdditionStaysAtShell' DASHI/Physics/Closure/NSTriadKNLuoShellGradedLocalCompatibilityExact.agda
grep -q 'localWeightedAbsorption' DASHI/Physics/Closure/NSTriadKNLuoWeightedIntegratedAbsorptionSummationExact.agda
grep -q 'weightedAbsorptionSummation' DASHI/Physics/Closure/NSTriadKNLuoWeightedIntegratedAbsorptionSummationExact.agda
grep -q 'strictViscosityMargin' DASHI/Physics/Closure/NSTriadKNLuoWeightedIntegratedAbsorptionSummationExact.agda
grep -q 'cubicDifferenceIdentity' DASHI/Physics/Closure/NSTriadKNLuoCubicTransferStrongLimitInterfaceExact.agda
grep -q 'cubicTransferDifferenceBound' DASHI/Physics/Closure/NSTriadKNLuoCubicTransferStrongLimitInterfaceExact.agda
grep -q 'exactFactorConvergenceImpliesExactCubicTransfer' DASHI/Physics/Closure/NSTriadKNLuoCubicTransferStrongLimitInterfaceExact.agda

grep -q '10.24033/asens.1404' DASHI/Physics/Closure/NSTriadKNLuoShellGradedLocalCompatibilityExact.agda
grep -q '10.20944/preprints202603.1591.v1' DASHI/Physics/Closure/NSTriadKNLuoWeightedIntegratedAbsorptionSummationExact.agda
grep -q '10.1090/chel/343' DASHI/Physics/Closure/NSTriadKNLuoCubicTransferStrongLimitInterfaceExact.agda
grep -q 'finiteWeightedSumDoesNotProveInfiniteSobolevSummability' DASHI/Physics/Closure/NSTriadKNLuoWeightedIntegratedAbsorptionSummationExact.agda
grep -q 'weakLinearConvergenceDoesNotSupplyThreeProductBounds' DASHI/Physics/Closure/NSTriadKNLuoCubicTransferStrongLimitInterfaceExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoIntegratedAbsorptionRound18Validation.agda
