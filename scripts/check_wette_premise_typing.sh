#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Core/RulePremiseTypingGeometryExact.agda
  DASHI/Foundations/Wette1969HistoricalSignatureExact.agda
  DASHI/Foundations/Wette1969JudgementConstructorsExact.agda
  DASHI/Foundations/Wette1969CriticalRuleDependencyExact.agda
  DASHI/Foundations/Wette1969CriticalPremiseTypingExact.agda
  DASHI/Foundations/Wette1969InitialRuleTranscriptionExact.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required premise typing source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q 'premiseKindsCanBeRecoveredBeforeBodiesIsTrue' DASHI/Core/RulePremiseTypingGeometryExact.agda
grep -q 'typedRequirementIsAlreadyExactPremiseBodyIsFalse' DASHI/Core/RulePremiseTypingGeometryExact.agda
grep -q 'partialTypingReceiptIsAlreadyCompleteRuleIsFalse' DASHI/Core/RulePremiseTypingGeometryExact.agda

grep -q 'DOI: 10.1007/978-3-642-86745-3_9' DASHI/Foundations/Wette1969JudgementConstructorsExact.agda
grep -q 'allHistoricalRelatorAritiesHaveTypedConstructorsIsTrue' DASHI/Foundations/Wette1969JudgementConstructorsExact.agda
grep -q 'constructorLayerAddsSemanticTruthIsFalse' DASHI/Foundations/Wette1969JudgementConstructorsExact.agda
grep -q 'typedConstructorAlreadyRecoversCriticalRuleArgumentsIsFalse' DASHI/Foundations/Wette1969JudgementConstructorsExact.agda

grep -q 'DOI: 10.1007/978-3-642-86745-3_9' DASHI/Foundations/Wette1969CriticalPremiseTypingExact.agda
grep -q 'rule9324x25FourPremiseKindsRecoveredIsTrue' DASHI/Foundations/Wette1969CriticalPremiseTypingExact.agda
grep -q 'rule915Premises24x25TypedAsSubstitutionJudgementsIsTrue' DASHI/Foundations/Wette1969CriticalPremiseTypingExact.agda
grep -q 'judgementKindRecoveryAlreadySuppliesExactFormulaArgumentsIsFalse' DASHI/Foundations/Wette1969CriticalPremiseTypingExact.agda
grep -q 'premiseTypingAlreadySuppliesExecutableSubstitutionIsFalse' DASHI/Foundations/Wette1969CriticalPremiseTypingExact.agda
grep -q 'sharedJudgementConstructorOwnerReusedIsTrue' DASHI/Foundations/Wette1969InitialRuleTranscriptionExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Core/RulePremiseTypingGeometryExact.agda \
  DASHI/Foundations/Wette1969JudgementConstructorsExact.agda \
  DASHI/Foundations/Wette1969CriticalPremiseTypingExact.agda \
  DASHI/Foundations/Wette1969InitialRuleTranscriptionExact.agda
