#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Physics/YangMills/BalabanP33LiteralGaugeConstraintCancellationExact.agda
  DASHI/Physics/YangMills/BalabanP33WilsonSharpBudgetCoercivityExact.agda
  DASHI/Physics/YangMills/BalabanP33LiteralPhysicalPerturbationAdapterExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound21Validation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "round twenty-one compatibility root contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

checks=(
  'BalabanP33LiteralGaugeConstraintCancellationExact.agda:residualFirstNormSquaredNonnegative'
  'BalabanP33LiteralGaugeConstraintCancellationExact.agda:constraintCancellationLeavesWilsonGaugeHodgeExact'
  'BalabanP33LiteralGaugeConstraintCancellationExact.agda:flatHodgeOldRemainderIsNegativeGauge'
  'BalabanP33LiteralGaugeConstraintCancellationExact.agda:oldShortcutUnitGaugeWitness'
  'BalabanP33LiteralGaugeConstraintCancellationExact.agda:literalHessianCoerciveFromWilsonGaugeHodgeDifference'
  'BalabanP33WilsonSharpBudgetCoercivityExact.agda:sharpWilsonGaugeBudgetExact'
  'BalabanP33WilsonSharpBudgetCoercivityExact.agda:sharpWilsonGaugeBudgetPlusGapIsPhysicalFloor'
  'BalabanP33WilsonSharpBudgetCoercivityExact.agda:coupledSignedLowerFromSeparateBudgets'
  'BalabanP33WilsonSharpBudgetCoercivityExact.agda:sharpCoupledLowerImpliesPhysicalSignedLower'
  'BalabanP33WilsonSharpBudgetCoercivityExact.agda:physicalBondNormSqNonnegative'
  'BalabanP33WilsonSharpBudgetCoercivityExact.agda:literalHessianCoerciveFromSharpWilsonGaugeBudgets'
  'BalabanP33LiteralPhysicalPerturbationAdapterExact.agda:LiteralPhysicalPerturbationModel'
  'BalabanP33LiteralPhysicalPerturbationAdapterExact.agda:literalHessianCoerciveFromSamePhysicalPerturbation'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

grep -q '10.1103/PhysRevD.10.2445' \
  DASHI/Physics/YangMills/BalabanP33LiteralGaugeConstraintCancellationExact.agda
grep -q '10.1007/BF01466594' \
  DASHI/Physics/YangMills/BalabanP33LiteralGaugeConstraintCancellationExact.agda
grep -q '10.1007/BF01211042' \
  DASHI/Physics/YangMills/BalabanP33LiteralGaugeConstraintCancellationExact.agda
grep -q '10.1007/BF01240355' \
  DASHI/Physics/YangMills/BalabanP33WilsonSharpBudgetCoercivityExact.agda
grep -q '1549/196608' \
  DASHI/Physics/YangMills/BalabanP33WilsonSharpBudgetCoercivityExact.agda
grep -q '4595/196608' \
  DASHI/Physics/YangMills/BalabanP33WilsonSharpBudgetCoercivityExact.agda
grep -q 'former overmatched' \
  DASHI/Physics/YangMills/BalabanP33LiteralGaugeConstraintCancellationExact.agda
grep -q 'same non-phantom h' \
  DASHI/Physics/YangMills/BalabanP33LiteralPhysicalPerturbationAdapterExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound21Validation.agda
