#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Foundations/Wette1969FiniteDerivationContextExact.agda
  DASHI/Foundations/Wette1969DerivationClosureExact.agda
  DASHI/Foundations/Wette1969SchematicSubstitutionFreshnessExact.agda
  DASHI/Foundations/Wette1969OrderedTuplePredicateSubstitutionExact.agda
  DASHI/Foundations/Wette1969ObjectVariableMarkWordsExact.agda
  DASHI/Foundations/Wette1969QuantifierCaptureSafetyExact.agda
  DASHI/Foundations/Wette1969RecursorBindingScopeExact.agda
  DASHI/Foundations/Wette1969DependentTwoStageSubstitutionExact.agda
  DASHI/Foundations/Wette1969Rule9324x25PremiseTemplateExact.agda
  DASHI/Foundations/Wette1969Rule9324x25ComputationalSideConditionsExact.agda
  DASHI/Foundations/Wette1969Rule828To9324x25DerivationExact.agda
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

grep -q 'schematicWordVariableSubstitutionNowExecutableIsTrue' DASHI/Foundations/Wette1969SchematicSubstitutionFreshnessExact.agda
grep -q 'tupleThenPredicateOrderNowExecutableIsTrue' DASHI/Foundations/Wette1969OrderedTuplePredicateSubstitutionExact.agda
grep -q 'boundedStructuralNonCommutationIsFullHistoricalSubstitutionTheoremIsFalse' DASHI/Foundations/Wette1969OrderedTuplePredicateSubstitutionExact.agda

grep -q 'objectVariableConstructorRecoveredFromRule3IsTrue' DASHI/Foundations/Wette1969ObjectVariableMarkWordsExact.agda
grep -q 'predicateMarkConstructorRecoveredFromRule4IsTrue' DASHI/Foundations/Wette1969ObjectVariableMarkWordsExact.agda
grep -q 'objectSyntaxSeparatedFromRuleSchematicWordVariablesIsTrue' DASHI/Foundations/Wette1969ObjectVariableMarkWordsExact.agda
grep -q 'proofRelevantObjectSyntaxRecognitionNowAvailableIsTrue' DASHI/Foundations/Wette1969ObjectVariableMarkWordsExact.agda

grep -q 'sourceQuantifierCaptureCriterionNowTypedIsTrue' DASHI/Foundations/Wette1969QuantifierCaptureSafetyExact.agda
grep -q 'directCaptureRiskRefutesSafetyIsTrue' DASHI/Foundations/Wette1969QuantifierCaptureSafetyExact.agda
grep -q 'recursorBindingRegimeAlreadyIncludedIsFalse' DASHI/Foundations/Wette1969QuantifierCaptureSafetyExact.agda

grep -q 'recursorScopePartitionNowSourceRecoveredIsTrue' DASHI/Foundations/Wette1969RecursorBindingScopeExact.agda
grep -q 'exactRecursorBinderPackagePiXRecoveredIsTrue' DASHI/Foundations/Wette1969RecursorBindingScopeExact.agda
grep -q 'predicateMarkAndVariableTupleTargetsSeparatedIsTrue' DASHI/Foundations/Wette1969RecursorBindingScopeExact.agda
grep -q 'exactRecursorBinderTargetParserNowRecoveredIsTrue' DASHI/Foundations/Wette1969RecursorBindingScopeExact.agda
grep -q 'wholeCPRPrefixIsInsideRecursorBindingScopeIsFalse' DASHI/Foundations/Wette1969RecursorBindingScopeExact.agda

grep -q 'secondStageSafetyIndexedByActualIntermediateIsTrue' DASHI/Foundations/Wette1969DependentTwoStageSubstitutionExact.agda
grep -q 'rule828SequentialCompositionNowTypedIsTrue' DASHI/Foundations/Wette1969DependentTwoStageSubstitutionExact.agda
grep -q 'pairedFourPlaceIIJudgementNowReproducedIsTrue' DASHI/Foundations/Wette1969DependentTwoStageSubstitutionExact.agda
grep -q 'sourceOrderV2ToV3ThenW2ToRecursivePredicatePreservedIsTrue' DASHI/Foundations/Wette1969DependentTwoStageSubstitutionExact.agda
grep -q 'typedIIFormulaIsAlreadyHistoricalDerivabilityProofIsFalse' DASHI/Foundations/Wette1969DependentTwoStageSubstitutionExact.agda

grep -q 'premise4HasIndependentPairedSubstituendAndReplacementIsTrue' DASHI/Foundations/Wette1969Rule9324x25PremiseTemplateExact.agda
grep -q 'freshTupleIsDefinitionallyWholePremise4ReplacementIsFalse' DASHI/Foundations/Wette1969Rule9324x25PremiseTemplateExact.agda

grep -q 'premise3FreshnessFragmentNowComputationallyCertifiableIsTrue' DASHI/Foundations/Wette1969Rule9324x25ComputationalSideConditionsExact.agda
grep -q 'computationalCertificateIsAlreadyHistoricalDerivabilityProofIsFalse' DASHI/Foundations/Wette1969Rule9324x25ComputationalSideConditionsExact.agda

grep -q 'rule828ConclusionDefinitionallyMatchesCriticalPremise4IsTrue' DASHI/Foundations/Wette1969Rule828To9324x25DerivationExact.agda
grep -q 'pairedIIPremiseGeneratedInsideDerivationContextIsTrue' DASHI/Foundations/Wette1969Rule828To9324x25DerivationExact.agda
grep -q 'firstThreeCriticalPremisesPersistAcrossRule828IsTrue' DASHI/Foundations/Wette1969Rule828To9324x25DerivationExact.agda
grep -q 'certified828Then9324And9325TracesNowConstructibleIsTrue' DASHI/Foundations/Wette1969Rule828To9324x25DerivationExact.agda
grep -q 'criticalPremise4StillMustBeSuppliedExternallyAfterRule828IsFalse' DASHI/Foundations/Wette1969Rule828To9324x25DerivationExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Foundations/Wette1969DerivationClosureExact.agda \
  DASHI/Foundations/Wette1969SchematicSubstitutionFreshnessExact.agda \
  DASHI/Foundations/Wette1969OrderedTuplePredicateSubstitutionExact.agda \
  DASHI/Foundations/Wette1969ObjectVariableMarkWordsExact.agda \
  DASHI/Foundations/Wette1969QuantifierCaptureSafetyExact.agda \
  DASHI/Foundations/Wette1969RecursorBindingScopeExact.agda \
  DASHI/Foundations/Wette1969DependentTwoStageSubstitutionExact.agda \
  DASHI/Foundations/Wette1969Rule9324x25PremiseTemplateExact.agda \
  DASHI/Foundations/Wette1969Rule9324x25ComputationalSideConditionsExact.agda \
  DASHI/Foundations/Wette1969Rule828To9324x25DerivationExact.agda
