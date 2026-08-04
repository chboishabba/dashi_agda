#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Physics/YangMills/BalabanP33BishopHigherOrderTaylorExact.agda
  DASHI/Physics/YangMills/BalabanP33BishopInverseDexpNumeratorExact.agda
  DASHI/Physics/YangMills/BalabanP33BishopInverseDexpCoefficientExact.agda
  DASHI/Physics/YangMills/BalabanP33InverseDexpRadiusArithmeticExact.agda
  DASHI/Physics/YangMills/BalabanP33WilsonCrossArcBudgetExact.agda
  DASHI/Physics/YangMills/BalabanP33WilsonDiagonalBudgetExact.agda
  DASHI/Physics/YangMills/BalabanClayT5StagedDiagonalTailExact.agda
  DASHI/Physics/YangMills/BalabanClayT5CumulantLowerBoundNontrivialityExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaReuseExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound14Validation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas' "${files[@]}"; then
  echo "Clay highest-alpha round fourteen contains a postulate, hole, unsafe escape, or unsolved-meta option" >&2
  exit 1
fi

checks=(
  'BalabanP33BishopHigherOrderTaylorExact.agda:higherOrderTaylorBounds'
  'BalabanP33BishopHigherOrderTaylorExact.agda:sineSepticLower'
  'BalabanP33BishopHigherOrderTaylorExact.agda:cosineQuarticUpper'
  'BalabanP33BishopInverseDexpNumeratorExact.agda:inverseDexpNumeratorBounds'
  'BalabanP33BishopInverseDexpCoefficientExact.agda:crossMultipliedInverseDexpCoefficientBounds'
  'BalabanP33BishopInverseDexpCoefficientExact.agda:oneTwelfthDenominatorBelowNumerator'
  'BalabanP33BishopInverseDexpCoefficientExact.agda:numeratorBelowOneSixthDenominator'
  'BalabanP33InverseDexpRadiusArithmeticExact.agda:inverseDexpEnvelopeAtRadiusBelowRadius'
  'BalabanP33WilsonCrossArcBudgetExact.agda:orderedCrossArcOccurrenceCountExact'
  'BalabanP33WilsonCrossArcBudgetExact.agda:completeCrossBudgetIsHalfRadius'
  'BalabanP33WilsonDiagonalBudgetExact.agda:completeWilsonBudgetIsThreeQuarterRadius'
  'BalabanP33WilsonDiagonalBudgetExact.agda:completeWilsonBudgetPlusSlackIsRadius'
  'BalabanClayT5StagedDiagonalTailExact.agda:stagedTailsGiveDiagonalTail'
  'BalabanClayT5StagedDiagonalTailExact.agda:stagedDiagonalSequenceConverges'
  'BalabanClayT5CumulantLowerBoundNontrivialityExact.agda:uniformFiniteLowerBoundForcesContinuumNonzero'
  'BalabanClayT5CumulantLowerBoundNontrivialityExact.agda:continuumCumulantLowerBoundExcludesGaussian'
  'BalabanClayHighestAlphaReuseExact.agda:allScalePhysicalAdmissibility'
  'BalabanClayHighestAlphaReuseExact.agda:continuumOS2FromCompleteGramLimits'
  'BalabanClayHighestAlphaReuseExact.agda:positivePhysicalTransferGap'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

# External theorem provenance is required where each literature result enters.
grep -q 'arXiv:2205.08354' \
  DASHI/Physics/YangMills/BalabanP33BishopHigherOrderTaylorExact.agda
grep -q '10.1007/978-3-319-13467-3' \
  DASHI/Physics/YangMills/BalabanP33BishopInverseDexpCoefficientExact.agda
grep -q '10.1103/PhysRevD.10.2445' \
  DASHI/Physics/YangMills/BalabanP33WilsonCrossArcBudgetExact.agda
grep -q '10.1007/BF01240355' \
  DASHI/Physics/YangMills/BalabanP33WilsonCrossArcBudgetExact.agda
grep -q '10.1007/BF01239022' \
  DASHI/Physics/YangMills/BalabanClayT5StagedDiagonalTailExact.agda
grep -q '10.1007/BF01645738' \
  DASHI/Physics/YangMills/BalabanClayT5CumulantLowerBoundNontrivialityExact.agda
grep -q '10.1007/BF01217741' \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaReuseExact.agda
grep -q '10.1007/BF01221251' \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaReuseExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound14Validation.agda
