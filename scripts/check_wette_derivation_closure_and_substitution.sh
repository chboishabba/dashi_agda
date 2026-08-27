#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Foundations/Wette1969FiniteDerivationContextExact.agda
  DASHI/Foundations/Wette1969DerivationClosureExact.agda
  DASHI/Foundations/Wette1969SchematicSubstitutionFreshnessExact.agda
  DASHI/Foundations/Wette1969OrderedTuplePredicateSubstitutionExact.agda
  DASHI/Foundations/Wette1969QuantifierCaptureSafetyExact.agda
  DASHI/Foundations/Wette1969RecursorBindingScopeExact.agda
  DASHI/Foundations/Wette1969Rule9324x25ComputationalSideConditionsExact.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required Wette closure/substitution source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q 'certifiedConclusionGeneratesLaterMembershipEvidenceIsTrue' DASHI/Foundations/Wette1969DerivationClosureExact.agda
grep -q 'priorFormulaePersistAcrossWholeCertifiedTraceIsTrue' DASHI/Foundations/Wette1969DerivationClosureExact.agda
grep -q 'earlierCertifiedConclusionsPersistToTraceTargetIsTrue' DASHI/Foundations/Wette1969DerivationClosureExact.agda
grep -q 'finiteClosureAlreadyDecidesAllHistoricalPremisesIsFalse' DASHI/Foundations/Wette1969DerivationClosureExact.agda

grep -q 'DOI: 10.1007/978-3-642-86745-3_9' DASHI/Foundations/Wette1969SchematicSubstitutionFreshnessExact.agda
grep -q 'schematicWordVariableSubstitutionNowExecutableIsTrue' DASHI/Foundations/Wette1969SchematicSubstitutionFreshnessExact.agda
grep -q 'freshnessCertificatesNowProofRelevantIsTrue' DASHI/Foundations/Wette1969SchematicSubstitutionFreshnessExact.agda
grep -q 'evaluatorAlreadyImplementsFullObjectLanguageTupleSubstitutionIsFalse' DASHI/Foundations/Wette1969SchematicSubstitutionFreshnessExact.agda

grep -q 'tupleThenPredicateOrderNowExecutableIsTrue' DASHI/Foundations/Wette1969OrderedTuplePredicateSubstitutionExact.agda
grep -q 'structuralOrderSensitivityWitnessNowExistsIsTrue' DASHI/Foundations/Wette1969OrderedTuplePredicateSubstitutionExact.agda
grep -q 'sourceOrderRequirementNowHasConcreteComputationalWitnessIsTrue' DASHI/Foundations/Wette1969OrderedTuplePredicateSubstitutionExact.agda
grep -q 'boundedStructuralNonCommutationIsFullHistoricalSubstitutionTheoremIsFalse' DASHI/Foundations/Wette1969OrderedTuplePredicateSubstitutionExact.agda

grep -q 'sourceQuantifierCaptureCriterionNowTypedIsTrue' DASHI/Foundations/Wette1969QuantifierCaptureSafetyExact.agda
grep -q 'freeOccurrenceRespectsParticularizerAndGeneralizerBindingIsTrue' DASHI/Foundations/Wette1969QuantifierCaptureSafetyExact.agda
grep -q 'directCaptureRiskRefutesSafetyIsTrue' DASHI/Foundations/Wette1969QuantifierCaptureSafetyExact.agda
grep -q 'recursorBindingRegimeAlreadyIncludedIsFalse' DASHI/Foundations/Wette1969QuantifierCaptureSafetyExact.agda
grep -q 'existingSchematicEvaluatorAlreadyDischargesQuantifierCaptureSafetyIsFalse' DASHI/Foundations/Wette1969QuantifierCaptureSafetyExact.agda

grep -q 'recursorScopePartitionNowSourceRecoveredIsTrue' DASHI/Foundations/Wette1969RecursorBindingScopeExact.agda
grep -q 'recursorBindingRestrictedToDefiniensRegionIsTrue' DASHI/Foundations/Wette1969RecursorBindingScopeExact.agda
grep -q 'sourceAllowsVariableOrPredicateMarkCaptureAtRecursorIsTrue' DASHI/Foundations/Wette1969RecursorBindingScopeExact.agda
grep -q 'exactRecursorBinderTargetParserNowRecoveredIsFalse' DASHI/Foundations/Wette1969RecursorBindingScopeExact.agda

grep -q 'premise3FreshnessFragmentNowComputationallyCertifiableIsTrue' DASHI/Foundations/Wette1969Rule9324x25ComputationalSideConditionsExact.agda
grep -q 'premise4SourceOrderedTuplePredicateFragmentNowCertifiableIsTrue' DASHI/Foundations/Wette1969Rule9324x25ComputationalSideConditionsExact.agda
grep -q 'computationalCertificateIsAlreadyHistoricalDerivabilityProofIsFalse' DASHI/Foundations/Wette1969Rule9324x25ComputationalSideConditionsExact.agda
grep -q 'orderedStructuralFragmentIsAlreadyBindingAwareHistoricalSubstitutionIsFalse' DASHI/Foundations/Wette1969Rule9324x25ComputationalSideConditionsExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Foundations/Wette1969DerivationClosureExact.agda \
  DASHI/Foundations/Wette1969SchematicSubstitutionFreshnessExact.agda \
  DASHI/Foundations/Wette1969OrderedTuplePredicateSubstitutionExact.agda \
  DASHI/Foundations/Wette1969QuantifierCaptureSafetyExact.agda \
  DASHI/Foundations/Wette1969RecursorBindingScopeExact.agda \
  DASHI/Foundations/Wette1969Rule9324x25ComputationalSideConditionsExact.agda
