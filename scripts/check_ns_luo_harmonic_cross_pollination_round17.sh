#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_ns_luo_physical_carrier_round16.sh

files=(
  DASHI/Physics/Common/FiniteRingScaleDualityExact.agda
  DASHI/Physics/Common/ScaledFilteredEstimateExact.agda
  DASHI/Physics/Common/SeparatingProbeFamilyExact.agda
  DASHI/Physics/Common/FiniteWreathRefinementExact.agda
  DASHI/Physics/Common/FiniteThreeCycleTorusExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFourInteractionSeparatingProbeExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoRelativeScaleProbeCrossPollinationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoGalerkinScaledFiltrationCrossPollinationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoThreeCycleTorusCrossPollinationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoHarmonicCrossPollinationRound17Validation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "round seventeen contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

grep -q 'triadicNineDualityExact' DASHI/Physics/Common/FiniteRingScaleDualityExact.agda
grep -q 'lossCorrectedTransportExact' DASHI/Physics/Common/ScaledFilteredEstimateExact.agda
grep -q 'pairProbesSeparate' DASHI/Physics/Common/SeparatingProbeFamilyExact.agda
grep -q 'localPermutationStepTwiceAt' DASHI/Physics/Common/FiniteWreathRefinementExact.agda
grep -q 'translationsCommute' DASHI/Physics/Common/FiniteThreeCycleTorusExact.agda
grep -q 'pullbacksCommuteAt' DASHI/Physics/Common/FiniteThreeCycleTorusExact.agda
grep -q 'interactionProbesSeparate' DASHI/Physics/Closure/NSTriadKNLuoFourInteractionSeparatingProbeExact.agda
grep -q 'fourInteractionProbeSystem' DASHI/Physics/Closure/NSTriadKNLuoFourInteractionSeparatingProbeExact.agda
grep -q 'branchProbeExact' DASHI/Physics/Closure/NSTriadKNLuoRelativeScaleProbeCrossPollinationExact.agda
grep -q 'weakBranchMatchesDisplayedHalfGap' DASHI/Physics/Closure/NSTriadKNLuoRelativeScaleProbeCrossPollinationExact.agda
grep -q 'selectedGalerkinDefectTendsToZero' DASHI/Physics/Closure/NSTriadKNLuoGalerkinScaledFiltrationCrossPollinationExact.agda
grep -q 'velocityTranslationsCommuteAt' DASHI/Physics/Closure/NSTriadKNLuoThreeCycleTorusCrossPollinationExact.agda
grep -q 'firstTranslationHasOrderThreeAt' DASHI/Physics/Closure/NSTriadKNLuoThreeCycleTorusCrossPollinationExact.agda
grep -q '10.24033/asens.1404' DASHI/Physics/Closure/NSTriadKNLuoFourInteractionSeparatingProbeExact.agda
grep -q '10.1007/978-3-642-16830-7' DASHI/Physics/Closure/NSTriadKNLuoRelativeScaleProbeCrossPollinationExact.agda
grep -q '10.2140/pjm.1982.98.333' DASHI/Physics/Closure/NSTriadKNLuoGalerkinScaledFiltrationCrossPollinationExact.agda
grep -q '10.1017/CBO9780511626265' DASHI/Physics/Closure/NSTriadKNLuoThreeCycleTorusCrossPollinationExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoHarmonicCrossPollinationRound17Validation.agda
