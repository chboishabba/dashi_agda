#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Core/RulePremiseDependencyGeometryExact.agda
  DASHI/Foundations/Wette1969RuleRevisionExact.agda
  DASHI/Foundations/Wette1969CriticalRuleDependencyExact.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "missing critical-rule source: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q 'onePremiseMaySupportMultipleObligationsIsTrue' DASHI/Core/RulePremiseDependencyGeometryExact.agda
grep -q 'overlappingPremiseSupportMakesObligationsDefinitionallyEqualIsFalse' DASHI/Core/RulePremiseDependencyGeometryExact.agda
grep -q 'premise18InductionRoleRecoveredIsTrue' DASHI/Foundations/Wette1969CriticalRuleDependencyExact.agda
grep -q 'premise27IndependenceRoleRecoveredIsTrue' DASHI/Foundations/Wette1969CriticalRuleDependencyExact.agda
grep -q 'premises10To15SupportBothMajorObligationsIsTrue' DASHI/Foundations/Wette1969CriticalRuleDependencyExact.agda
grep -q 'rules9324And9325ShareFourPremisesIsTrue' DASHI/Foundations/Wette1969CriticalRuleDependencyExact.agda
grep -q 'orderedSubstitutionRequirementRecoveredIsTrue' DASHI/Foundations/Wette1969CriticalRuleDependencyExact.agda
grep -q 'dependencyTranscriptionIsAlreadyExactFormulaBodyTranscriptionIsFalse' DASHI/Foundations/Wette1969CriticalRuleDependencyExact.agda
grep -q 'DOI: 10.1007/978-3-642-86745-3_9' DASHI/Foundations/Wette1969CriticalRuleDependencyExact.agda
grep -q 'DOI 10.2307/2272630' DASHI/Foundations/Wette1969CriticalRuleDependencyExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Core/RulePremiseDependencyGeometryExact.agda \
  DASHI/Foundations/Wette1969CriticalRuleDependencyExact.agda
