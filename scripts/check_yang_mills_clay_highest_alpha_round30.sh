#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_yang_mills_clay_highest_alpha_round29.sh

files=(
  DASHI/Physics/YangMills/BalabanStrongCouplingSUFourDimensionalMarginExact.agda
  DASHI/Physics/YangMills/BalabanStrongCouplingSU2ActionNormalizationExact.agda
  DASHI/Physics/YangMills/BalabanStrongCouplingBetaRhoSeparationExact.agda
  DASHI/Physics/YangMills/BalabanStrongCouplingPoincareBudgetExact.agda
  DASHI/Physics/YangMills/BalabanStrongCouplingSpaceTimeDecayBalanceExact.agda
  DASHI/Physics/YangMills/BalabanStrongCouplingVsContinuumRouteExact.agda
  DASHI/Physics/YangMills/YangMillsStrongCouplingAlternativeGateExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound30StrongCouplingFunctionalValidation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported' "${files[@]}"; then
  echo "round thirty contains a hole, postulate, unsafe escape, trust primitive, or imported theorem receipt" >&2
  exit 1
fi

checks=(
  'BalabanStrongCouplingSUFourDimensionalMarginExact.agda:fourDimensionalDiagonalCoefficientExact'
  'BalabanStrongCouplingSUFourDimensionalMarginExact.agda:fourDimensionalCrossCoefficientExact'
  'BalabanStrongCouplingSUFourDimensionalMarginExact.agda:diagonalPlusCrossIsTotal'
  'BalabanStrongCouplingSUFourDimensionalMarginExact.agda:thresholdSaturatesMargin'
  'BalabanStrongCouplingSUFourDimensionalMarginExact.agda:marginFactorsThroughThresholdSlack'
  'BalabanStrongCouplingSUFourDimensionalMarginExact.agda:configuredNormalizedMarginPositive'
  'BalabanStrongCouplingSU2ActionNormalizationExact.agda:su2ExponentIsConstantMinusWilsonPenalty'
  'BalabanStrongCouplingSU2ActionNormalizationExact.agda:configuredInteriorActionCoefficientExact'
  'BalabanStrongCouplingSU2ActionNormalizationExact.agda:exponentAndPenaltySecondVariationsOppose'
  'BalabanStrongCouplingBetaRhoSeparationExact.agda:rhoAgainstThresholdSlackExact'
  'BalabanStrongCouplingBetaRhoSeparationExact.agda:rhoSubstitutedNormalizedMarginExact'
  'BalabanStrongCouplingPoincareBudgetExact.agda:logSobolevIsTwicePoincare'
  'BalabanStrongCouplingPoincareBudgetExact.agda:covarianceSquareBudgetFactorsThroughVariances'
  'BalabanStrongCouplingPoincareBudgetExact.agda:configuredSU2InverseLaw'
  'BalabanStrongCouplingPoincareBudgetExact.agda:configuredSU2LeftInverseLaw'
  'BalabanStrongCouplingSpaceTimeDecayBalanceExact.agda:balancedSpatialDecompositionExact'
  'BalabanStrongCouplingSpaceTimeDecayBalanceExact.agda:balancedExponentsAgree'
  'BalabanStrongCouplingSpaceTimeDecayBalanceExact.agda:configuredCommonExponentExact'
  'BalabanStrongCouplingVsContinuumRouteExact.agda:unitInverseCouplingMarginExact'
  'BalabanStrongCouplingVsContinuumRouteExact.agda:stochasticRouteDoesNotSupplyCutoffRemoval'
  'YangMillsStrongCouplingAlternativeGateExact.agda:strongCouplingGapIsNotContinuumMeasure'
  'YangMillsStrongCouplingAlternativeGateExact.agda:finitePropagatorNotRequiredByStochasticEntry'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

grep -q '10.1007/s00220-022-04609-1' DASHI/Physics/YangMills/BalabanStrongCouplingSUFourDimensionalMarginExact.agda
grep -q '10.1103/PhysRevD.10.2445' DASHI/Physics/YangMills/BalabanStrongCouplingSU2ActionNormalizationExact.agda
grep -q '10.1007/BF01229381' DASHI/Physics/YangMills/BalabanStrongCouplingBetaRhoSeparationExact.agda
grep -q '10.1007/978-3-540-36107-7_1' DASHI/Physics/YangMills/BalabanStrongCouplingSpaceTimeDecayBalanceExact.agda
grep -q 'No canonical inhabitant' DASHI/Physics/YangMills/BalabanStrongCouplingBetaRhoSeparationExact.agda
grep -q 'does not identify beta with the small-field' DASHI/Physics/YangMills/BalabanStrongCouplingSU2ActionNormalizationExact.agda
grep -q 'Poincare alone is not' DASHI/Physics/YangMills/BalabanStrongCouplingPoincareBudgetExact.agda
grep -q 'does not supply those estimates' DASHI/Physics/YangMills/BalabanStrongCouplingSpaceTimeDecayBalanceExact.agda
grep -q 'fixed-lattice strong-coupling' DASHI/Physics/YangMills/BalabanStrongCouplingVsContinuumRouteExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound30StrongCouplingFunctionalValidation.agda
