#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Core/OrderedSubstitutionGeometryExact.agda
  DASHI/Foundations/Wette1969SubstitutionOrderExact.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "missing substitution-order source: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q 'sourceRequiredOrderAlreadyProvesSemanticNonCommutationIsFalse' DASHI/Core/OrderedSubstitutionGeometryExact.agda
grep -q 'conditionalOrderIndependenceIsRepresentableIsTrue' DASHI/Core/OrderedSubstitutionGeometryExact.agda
grep -q 'DOI: 10.1007/978-3-642-86745-3_9' DASHI/Foundations/Wette1969SubstitutionOrderExact.agda
grep -q 'rule9324x25OrderRequirementRecoveredIsTrue' DASHI/Foundations/Wette1969SubstitutionOrderExact.agda
grep -q 'rule915Premises24x25ConditionalOrderIndependenceRecoveredIsTrue' DASHI/Foundations/Wette1969SubstitutionOrderExact.agda
grep -q 'sourceOrderRequirementAlreadySuppliesHistoricalSubstitutionEvaluatorIsFalse' DASHI/Foundations/Wette1969SubstitutionOrderExact.agda
grep -q 'sourceOrderRequirementAlreadyProvesSemanticNonCommutationIsFalse' DASHI/Foundations/Wette1969SubstitutionOrderExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Core/OrderedSubstitutionGeometryExact.agda \
  DASHI/Foundations/Wette1969SubstitutionOrderExact.agda
