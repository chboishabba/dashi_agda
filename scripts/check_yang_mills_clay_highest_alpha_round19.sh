#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Physics/YangMills/BalabanP33FiniteCombesThomasConjugationExact.agda
  DASHI/Physics/YangMills/BalabanP33FiniteCombesThomasTiltBudgetExact.agda
  DASHI/Physics/YangMills/BalabanP33RationalGeometricCombesThomasWeightExact.agda
  DASHI/Physics/YangMills/BalabanP33CombesThomasCoercivitySurvivalExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalCombesThomasPromotionExact.agda
  DASHI/Physics/YangMills/BalabanP33BlockPoincareNormalizationWallExact.agda
  DASHI/Physics/YangMills/BalabanP33AugmentedYangMillsHessianStructureExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound19Validation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "round nineteen contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

checks=(
  'BalabanP33FiniteCombesThomasConjugationExact.agda:conjugateCommutesWithComposition'
  'BalabanP33FiniteCombesThomasConjugationExact.agda:conjugatedRightInverseWithStableIdentity'
  'BalabanP33FiniteCombesThomasConjugationExact.agda:tiltDefectVanishesOutsideOriginalSupport'
  'BalabanP33FiniteCombesThomasConjugationExact.agda:combesThomasKernelDecayFromTiltedEntry'
  'BalabanP33FiniteCombesThomasTiltBudgetExact.agda:tiltDefectFactorization'
  'BalabanP33FiniteCombesThomasTiltBudgetExact.agda:tiltDefectRowMassBound'
  'BalabanP33FiniteCombesThomasTiltBudgetExact.agda:p33TiltDefectBelowHalfGap'
  'BalabanP33RationalGeometricCombesThomasWeightExact.agda:rootedWeightInverseLaw'
  'BalabanP33RationalGeometricCombesThomasWeightExact.agda:unitShellRatioExact'
  'BalabanP33RationalGeometricCombesThomasWeightExact.agda:unitShellDistortionBound'
  'BalabanP33CombesThomasCoercivitySurvivalExact.agda:halfGapCoercivitySurvives'
  'BalabanP33CombesThomasCoercivitySurvivalExact.agda:p33TiltedCoercivityFromHalfGap'
  'BalabanP33CombesThomasCoercivitySurvivalExact.agda:p33TiltedInverseNormBound'
  'BalabanP33PhysicalCombesThomasPromotionExact.agda:physicalIdentityStable'
  'BalabanP33PhysicalCombesThomasPromotionExact.agda:physicalTiltDefectBelowHalfGap'
  'BalabanP33PhysicalCombesThomasPromotionExact.agda:physicalTiltedRightInverse'
  'BalabanP33PhysicalCombesThomasPromotionExact.agda:physicalGreenKernelDecay'
  'BalabanP33BlockPoincareNormalizationWallExact.agda:fourDimensionalUnscaledConstantWall'
  'BalabanP33BlockPoincareNormalizationWallExact.agda:fluctuationSquareModeForcesLinearCrossBound'
  'BalabanP33BlockPoincareNormalizationWallExact.agda:unboundedLowerBoundsRefuteUniformConstant'
  'BalabanP33AugmentedYangMillsHessianStructureExact.agda:augmentedHessianSymmetric'
  'BalabanP33AugmentedYangMillsHessianStructureExact.agda:augmentedCoercivityFromWilson'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

# Provenance and scope discipline.
grep -q '10.1007/BF01646473' \
  DASHI/Physics/YangMills/BalabanP33FiniteCombesThomasConjugationExact.agda
grep -q '10.1090/conm/476/09307' \
  DASHI/Physics/YangMills/BalabanP33FiniteCombesThomasTiltBudgetExact.agda
grep -q '10.1016/j.matpur.2012.02.001' \
  DASHI/Physics/YangMills/BalabanP33AugmentedYangMillsHessianStructureExact.agda
grep -q 'ai.viXra:2607.0042' \
  DASHI/Physics/YangMills/BalabanP33BlockPoincareNormalizationWallExact.agda
grep -q 'not used as an authority' \
  DASHI/Physics/YangMills/BalabanP33BlockPoincareNormalizationWallExact.agda
grep -q 'without introducing a variable rational denominator' \
  DASHI/Physics/YangMills/BalabanP33BlockPoincareNormalizationWallExact.agda
grep -q 'No collar M=21' \
  DASHI/Physics/YangMills/BalabanP33PhysicalCombesThomasPromotionExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound19Validation.agda
