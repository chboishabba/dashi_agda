#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_yang_mills_clay_highest_alpha_round26.sh

files=(
  DASHI/Physics/Common/FiniteRingScaleDualityExact.agda
  DASHI/Physics/Common/ScaledFilteredEstimateExact.agda
  DASHI/Physics/Common/SeparatingProbeFamilyExact.agda
  DASHI/Physics/Common/FiniteWreathRefinementExact.agda
  DASHI/Physics/Common/FiniteThreeCycleTorusExact.agda
  DASHI/Physics/YangMills/BalabanP33WilsonSixteenPlacementSeparatingProbeExact.agda
  DASHI/Physics/YangMills/BalabanP33ScaledFilteredCrossPollinationExact.agda
  DASHI/Physics/YangMills/BalabanP33WreathBlockSpinCrossPollinationExact.agda
  DASHI/Physics/YangMills/BalabanP33ThreeCycleBlockTorusCrossPollinationExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound27HarmonicCrossPollinationValidation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "round twenty seven contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

grep -q 'triadicNineDualityExact' DASHI/Physics/Common/FiniteRingScaleDualityExact.agda
grep -q 'lossCorrectedTransportExact' DASHI/Physics/Common/ScaledFilteredEstimateExact.agda
grep -q 'pairProbesSeparate' DASHI/Physics/Common/SeparatingProbeFamilyExact.agda
grep -q 'localPermutationStepTwiceAt' DASHI/Physics/Common/FiniteWreathRefinementExact.agda
grep -q 'translationsCommute' DASHI/Physics/Common/FiniteThreeCycleTorusExact.agda
grep -q 'pullbacksCommuteAt' DASHI/Physics/Common/FiniteThreeCycleTorusExact.agda
grep -q 'placementProbesSeparate' DASHI/Physics/YangMills/BalabanP33WilsonSixteenPlacementSeparatingProbeExact.agda
grep -q 'sixteenPlacementProbeSystem' DASHI/Physics/YangMills/BalabanP33WilsonSixteenPlacementSeparatingProbeExact.agda
grep -q 'totalPlacementCountIsSixteen' DASHI/Physics/YangMills/BalabanP33WilsonSixteenPlacementSeparatingProbeExact.agda
grep -q 'physicalStateAsSharedScale' DASHI/Physics/YangMills/BalabanP33ScaledFilteredCrossPollinationExact.agda
grep -q 'dyadicSharedPhysicalQuantityStable' DASHI/Physics/YangMills/BalabanP33ScaledFilteredCrossPollinationExact.agda
grep -q 'prototypeBlockSpinActionTwiceAt' DASHI/Physics/YangMills/BalabanP33WreathBlockSpinCrossPollinationExact.agda
grep -q 'blockTranslationsCommuteAt' DASHI/Physics/YangMills/BalabanP33ThreeCycleBlockTorusCrossPollinationExact.agda
grep -q 'blockFirstTranslationOrderThreeAt' DASHI/Physics/YangMills/BalabanP33ThreeCycleBlockTorusCrossPollinationExact.agda
grep -q '10.1007/BF01240221' DASHI/Physics/YangMills/BalabanP33WilsonSixteenPlacementSeparatingProbeExact.agda
grep -q '10.1017/CBO9781316036440' DASHI/Physics/YangMills/BalabanP33ScaledFilteredCrossPollinationExact.agda
grep -q '10.1007/978-1-4612-0731-3' DASHI/Physics/YangMills/BalabanP33WreathBlockSpinCrossPollinationExact.agda
grep -q '10.1017/CBO9780511626265' DASHI/Physics/YangMills/BalabanP33ThreeCycleBlockTorusCrossPollinationExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound27HarmonicCrossPollinationValidation.agda
