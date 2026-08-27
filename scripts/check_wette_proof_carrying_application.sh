#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Core/TypedDependencyCore.agda
  DASHI/Core/ProofCarryingRuleApplicationExact.agda
  DASHI/Foundations/Wette1969Rule9324x25PremiseTemplateExact.agda
  DASHI/Foundations/Wette1969ProofCarryingRuleApplicationExact.agda
  DASHI/Foundations/Wette1969FiniteDerivationContextExact.agda
  DASHI/Foundations/WetteFiniteDeductionTraceExact.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required proof-carrying rule source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q 'record AdmissibleAction' DASHI/Core/TypedDependencyCore.agda
grep -q 'typedDependencyCoreOwnsAdmissibilityIsTrue' DASHI/Core/ProofCarryingRuleApplicationExact.agda
grep -q 'selectedRuleCarriesApplicationProofIsTrue' DASHI/Core/ProofCarryingRuleApplicationExact.agda
grep -q 'laterTraceStepsAreIndexedByReachedStateIsTrue' DASHI/Core/ProofCarryingRuleApplicationExact.agda
grep -q 'ruleLabelAloneImpliesAdmissibilityIsFalse' DASHI/Core/ProofCarryingRuleApplicationExact.agda

grep -q 'DOI: 10.1007/978-3-642-86745-3_9' DASHI/Foundations/Wette1969ProofCarryingRuleApplicationExact.agda
grep -q 'typedDependencyCoreReusedForHistoricalAdmissibilityIsTrue' DASHI/Foundations/Wette1969ProofCarryingRuleApplicationExact.agda
grep -q 'historicalRuleSelectionCarriesAllPremiseEvidenceIsTrue' DASHI/Foundations/Wette1969ProofCarryingRuleApplicationExact.agda
grep -q 'rules9324And9325NowLiftToCertifiedContextTransitionsIsTrue' DASHI/Foundations/Wette1969ProofCarryingRuleApplicationExact.agda
grep -q 'bareHistoricalRuleBodyIsAlreadyAdmissibleAtEveryContextIsFalse' DASHI/Foundations/Wette1969ProofCarryingRuleApplicationExact.agda
grep -q 'certifiedContextTransitionAlreadyImplementsHistoricalSubstitutionIsFalse' DASHI/Foundations/Wette1969ProofCarryingRuleApplicationExact.agda

grep -q 'finiteContextMonotonicallyAccumulatesConclusionsIsTrue' DASHI/Foundations/Wette1969FiniteDerivationContextExact.agda
grep -q 'proofCarryingTraceErasesToExistingFiniteTraceIsTrue' DASHI/Foundations/Wette1969FiniteDerivationContextExact.agda
grep -q 'certifiedTraceProducesExistingFiniteDerivationWitnessIsTrue' DASHI/Foundations/Wette1969FiniteDerivationContextExact.agda
grep -q 'boolMachineAdmissibilityIsHistoricalRuleAuthorityIsFalse' DASHI/Foundations/Wette1969FiniteDerivationContextExact.agda
grep -q 'finiteContextMembershipIsAlreadySemanticTruthIsFalse' DASHI/Foundations/Wette1969FiniteDerivationContextExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Core/ProofCarryingRuleApplicationExact.agda \
  DASHI/Foundations/Wette1969ProofCarryingRuleApplicationExact.agda \
  DASHI/Foundations/Wette1969FiniteDerivationContextExact.agda

bash scripts/check_wette_derivation_closure_and_substitution.sh
