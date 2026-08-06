#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_conscious_access_round6_monster_filtered_carrier.sh

files=(
  DASHI/Physics/Common/FiniteRingScaleDualityExact.agda
  DASHI/Physics/Common/ScaledFilteredEstimateExact.agda
  DASHI/Physics/Common/SeparatingProbeFamilyExact.agda
  DASHI/Physics/Common/FiniteWreathRefinementExact.agda
  DASHI/Physics/Common/FiniteThreeCycleTorusExact.agda
  DASHI/Biology/BalancedTernaryHarmonicCarrierExact.agda
  DASHI/Biology/BalancedTernaryTorusWreathBridgeExact.agda
  DASHI/Biology/BalancedTernaryTetrationHarmonicBridgeExact.agda
  DASHI/Biology/JFineCoarseRelativeScaleExact.agda
  DASHI/Biology/JCompletionTrivialLineSeparationExact.agda
  DASHI/Biology/MonsterStructuredBulkCarrierExact.agda
  DASHI/Biology/MonsterSubgroupBranchingBenchmarksExact.agda
  DASHI/Biology/RestrictedGeneratorExpressionSymmetryExact.agda
  DASHI/Biology/ConsciousAccessRound7HarmonicWreathCarrierValidation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "round seven contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

checks=(
  'FiniteRingScaleDualityExact.agda:triadicNineDualityExact'
  'FiniteRingScaleDualityExact.agda:triadicNineAsTwoPlusSevenCocycle'
  'ScaledFilteredEstimateExact.agda:rescaleRepresentation'
  'ScaledFilteredEstimateExact.agda:lossCorrectedTransportExact'
  'SeparatingProbeFamilyExact.agda:pairProbesSeparate'
  'FiniteWreathRefinementExact.agda:localPermutationStepTwiceAt'
  'FiniteThreeCycleTorusExact.agda:translateFirstCubed'
  'FiniteThreeCycleTorusExact.agda:translateSecondCubed'
  'FiniteThreeCycleTorusExact.agda:translationsCommute'
  'FiniteThreeCycleTorusExact.agda:pullbacksCommuteAt'
  'BalancedTernaryHarmonicCarrierExact.agda:coarseChannelCountIsTen'
  'BalancedTernaryHarmonicCarrierExact.agda:jFine'
  'BalancedTernaryHarmonicCarrierExact.agda:elementaryHarmonicDimensionIs196830'
  'BalancedTernaryTorusWreathBridgeExact.agda:decodeEncodeChannel'
  'BalancedTernaryTorusWreathBridgeExact.agda:completionJFixedByFirstTranslation'
  'BalancedTernaryTorusWreathBridgeExact.agda:completionJFixedBySecondTranslation'
  'BalancedTernaryTetrationHarmonicBridgeExact.agda:jFineEvaluation'
  'BalancedTernaryTetrationHarmonicBridgeExact.agda:jFineEvaluationFibreMatchesRelativeScale'
  'BalancedTernaryTetrationHarmonicBridgeExact.agda:existingTowerLevelTwoHasNineToNineSites'
  'BalancedTernaryTetrationHarmonicBridgeExact.agda:recursiveSelfIndexingTetration'
  'JFineCoarseRelativeScaleExact.agda:jAbsoluteFineIsCoarseTimesJFine'
  'JFineCoarseRelativeScaleExact.agda:jFineIsCoarseTimesRelative'
  'JFineCoarseRelativeScaleExact.agda:jNineStepDualProductIsOne'
  'JCompletionTrivialLineSeparationExact.agda:unitRolesHaveEqualMultiplicity'
  'JCompletionTrivialLineSeparationExact.agda:unitRolesAreDistinct'
  'JCompletionTrivialLineSeparationExact.agda:coarseChannelCountExact'
  'JCompletionTrivialLineSeparationExact.agda:completionFineContributionExact'
  'JCompletionTrivialLineSeparationExact.agda:unreducedCarrierDimensionExact'
  'MonsterStructuredBulkCarrierExact.agda:structuredTotalDimensionExact'
  'MonsterStructuredBulkCarrierExact.agda:threePowerElevenPlusThreePowerNinePlusFiftyThree'
  'MonsterSubgroupBranchingBenchmarksExact.agda:characterValuesMatchedOnRepresentatives'
  'MonsterSubgroupBranchingBenchmarksExact.agda:threeALaneIsDistinct'
  'MonsterSubgroupBranchingBenchmarksExact.agda:threeBLaneIsDistinct'
  'MonsterSubgroupBranchingBenchmarksExact.agda:threeCLaneIsDistinct'
  'RestrictedGeneratorExpressionSymmetryExact.agda:cyclicDigitThirdPower'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  if [[ -f "DASHI/Biology/$file" ]]; then
    grep -q "$theorem" "DASHI/Biology/$file"
  else
    grep -q "$theorem" "DASHI/Physics/Common/$file"
  fi
done

grep -q '10.1017/CBO9780511626265' DASHI/Physics/Common/FiniteRingScaleDualityExact.agda
grep -q '10.1017/CBO9780511626265' DASHI/Physics/Common/FiniteThreeCycleTorusExact.agda
grep -q '10.1137/1.9781611970104' DASHI/Biology/BalancedTernaryHarmonicCarrierExact.agda
grep -q '10.1090/surv/117' DASHI/Biology/BalancedTernaryTetrationHarmonicBridgeExact.agda
grep -q '10.1007/978-1-4612-0731-3' DASHI/Physics/Common/FiniteWreathRefinementExact.agda
grep -q '10.1007/978-1-4612-0979-9' DASHI/Biology/JCompletionTrivialLineSeparationExact.agda
grep -q '10.1017/S1446788700031323' DASHI/Biology/MonsterSubgroupBranchingBenchmarksExact.agda
grep -q '10.48550/arXiv.2412.12182' DASHI/Biology/MonsterSubgroupBranchingBenchmarksExact.agda
grep -q 'tenIsPrimitiveSymmetryMultiplicityIsFalse' DASHI/Biology/MonsterFilteredCarrierExact.agda
grep -q 'elementaryChannelCarrierDoesNotEqualFullAssignmentSpace' DASHI/Biology/BalancedTernaryHarmonicCarrierExact.agda
grep -q 'jIsNotTenthOrdinaryTorusResidue' DASHI/Biology/BalancedTernaryTorusWreathBridgeExact.agda
grep -q 'elementaryChannelsAreNotFullConfigurations' DASHI/Biology/BalancedTernaryTetrationHarmonicBridgeExact.agda
grep -q 'jFineIsNotAbsoluteFineCarrier' DASHI/Biology/JFineCoarseRelativeScaleExact.agda
grep -q 'unitRolesAreDistinct' DASHI/Biology/JCompletionTrivialLineSeparationExact.agda
grep -q 'structuredChannelsAreNotClaimedMonsterInvariantSummands' DASHI/Biology/MonsterStructuredBulkCarrierExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/ConsciousAccessRound7HarmonicWreathCarrierValidation.agda
