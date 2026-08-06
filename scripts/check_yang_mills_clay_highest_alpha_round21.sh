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
  echo "round twenty-one contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

checks=(
  'BalabanP33LiteralGaugeConstraintCancellationExact.agda:residualFirstNormSquaredNonnegative'
  'BalabanP33LiteralGaugeConstraintCancellationExact.agda:matchedGaugeConstraintCancellationExact'
  'BalabanP33LiteralGaugeConstraintCancellationExact.agda:matchedReferenceRecomposesExactHessian'
  'BalabanP33LiteralGaugeConstraintCancellationExact.agda:literalHessianCoerciveFromWilsonDifference'
  'BalabanP33WilsonSharpBudgetCoercivityExact.agda:sharpBudgetPlusGapIsPhysicalFloor'
  'BalabanP33WilsonSharpBudgetCoercivityExact.agda:sharpWilsonBudgetBelowPhysicalFloor'
  'BalabanP33WilsonSharpBudgetCoercivityExact.agda:negateOrderReverse'
  'BalabanP33WilsonSharpBudgetCoercivityExact.agda:sharpSignedLowerImpliesPhysicalSignedLower'
  'BalabanP33WilsonSharpBudgetCoercivityExact.agda:globalNormSqNonnegative'
  'BalabanP33WilsonSharpBudgetCoercivityExact.agda:bondNormSqNonnegative'
  'BalabanP33WilsonSharpBudgetCoercivityExact.agda:literalHessianCoerciveFromSharpWilsonBudget'
  'BalabanP33LiteralPhysicalPerturbationAdapterExact.agda:LiteralPhysicalPerturbationModel'
  'BalabanP33LiteralPhysicalPerturbationAdapterExact.agda:literalWilsonDifferenceMatchesPhysical'
  'BalabanP33LiteralPhysicalPerturbationAdapterExact.agda:literalHessianCoerciveFromPhysicalWilsonDifference'
  'BalabanP33LiteralPhysicalPerturbationAdapterExact.agda:literalHessianCoerciveFromPhysicalSharpWilsonBudget'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

# Provenance and scope discipline.
grep -q '10.1103/PhysRevD.10.2445' \
  DASHI/Physics/YangMills/BalabanP33LiteralGaugeConstraintCancellationExact.agda
grep -q '10.1007/BF01466594' \
  DASHI/Physics/YangMills/BalabanP33LiteralGaugeConstraintCancellationExact.agda
grep -q '10.1007/BF01211042' \
  DASHI/Physics/YangMills/BalabanP33LiteralGaugeConstraintCancellationExact.agda
grep -q '10.1007/BF01240355' \
  DASHI/Physics/YangMills/BalabanP33WilsonSharpBudgetCoercivityExact.agda
grep -q '6131/196608' \
  DASHI/Physics/YangMills/BalabanP33WilsonSharpBudgetCoercivityExact.agda
grep -q 'one signed Wilson comparison' \
  DASHI/Physics/YangMills/BalabanP33LiteralGaugeConstraintCancellationExact.agda
grep -q 'sole analytic producer' \
  DASHI/Physics/YangMills/BalabanP33WilsonSharpBudgetCoercivityExact.agda
grep -q 'h is therefore not phantom' \
  DASHI/Physics/YangMills/BalabanP33LiteralPhysicalPerturbationAdapterExact.agda
grep -q 'same h' \
  DASHI/Physics/YangMills/BalabanP33LiteralPhysicalPerturbationAdapterExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound21Validation.agda
