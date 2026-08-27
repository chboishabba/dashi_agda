#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Core/ProofCarryingRuleApplicationExact.agda
  DASHI/Foundations/Wette1969FiniteDerivationContextExact.agda
  DASHI/Foundations/Wette1969DerivationClosureExact.agda
  DASHI/Foundations/Wette1969Rule915PredicateProducerExact.agda
  DASHI/Foundations/Wette1969Rule83TupleDerivationExact.agda
  DASHI/Foundations/Wette1969Rule8112FreshnessDerivationExact.agda
  DASHI/Foundations/Wette1969SchematicSubstitutionFreshnessExact.agda
  DASHI/Foundations/Wette1969OrderedTuplePredicateSubstitutionExact.agda
  DASHI/Foundations/Wette1969ObjectVariableMarkWordsExact.agda
  DASHI/Foundations/Wette1969QuantifierCaptureSafetyExact.agda
  DASHI/Foundations/Wette1969RecursorBindingScopeExact.agda
  DASHI/Foundations/Wette1969DependentTwoStageSubstitutionExact.agda
  DASHI/Foundations/Wette1969Rule9324x25PremiseTemplateExact.agda
  DASHI/Foundations/Wette1969Rule9324x25ComputationalSideConditionsExact.agda
  DASHI/Foundations/Wette1969Rule828To9324x25DerivationExact.agda
  DASHI/Foundations/Wette1969CriticalPremiseLocalDerivationExact.agda
  DASHI/Foundations/Wette1969CriticalPremiseConcreteProducerChainExact.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required Wette closure/substitution source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q 'certifiedTracesComposeAtActualReachedStateIsTrue' DASHI/Core/ProofCarryingRuleApplicationExact.agda

grep -q 'certifiedConclusionGeneratesLaterMembershipEvidenceIsTrue' DASHI/Foundations/Wette1969DerivationClosureExact.agda
grep -q 'priorFormulaePersistAcrossWholeCertifiedTraceIsTrue' DASHI/Foundations/Wette1969DerivationClosureExact.agda
grep -q 'finiteClosureAlreadyDecidesAllHistoricalPremisesIsFalse' DASHI/Foundations/Wette1969DerivationClosureExact.agda

grep -q 'rule915AddressCountAndPredicateOutputNowTypedIsTrue' DASHI/Foundations/Wette1969Rule915PredicateProducerExact.agda
grep -q 'certified915ApplicationGeneratesPredicateSchemaPremiseIsTrue' DASHI/Foundations/Wette1969Rule915PredicateProducerExact.agda
grep -q 'allTwentySevenPremiseBodiesNowLiteralOCRPerfectIsFalse' DASHI/Foundations/Wette1969Rule915PredicateProducerExact.agda

grep -q 'rules831And832NowLiteralHistoricalBodiesIsTrue' DASHI/Foundations/Wette1969Rule83TupleDerivationExact.agda
grep -q 'tupleFormationNowHasProofCarryingHistoricalStepsIsTrue' DASHI/Foundations/Wette1969Rule83TupleDerivationExact.agda

grep -q 'rules8112And8113NowLiteralHistoricalBodiesIsTrue' DASHI/Foundations/Wette1969Rule8112FreshnessDerivationExact.agda
grep -q 'tupleFreshnessCanBeGeneratedFromComponentFreshnessIsTrue' DASHI/Foundations/Wette1969Rule8112FreshnessDerivationExact.agda

grep -q 'secondStageSafetyIndexedByActualIntermediateIsTrue' DASHI/Foundations/Wette1969DependentTwoStageSubstitutionExact.agda
grep -q 'pairedFourPlaceIIJudgementNowReproducedIsTrue' DASHI/Foundations/Wette1969DependentTwoStageSubstitutionExact.agda

grep -q 'rule828ConclusionDefinitionallyMatchesCriticalPremise4IsTrue' DASHI/Foundations/Wette1969Rule828To9324x25DerivationExact.agda
grep -q 'criticalPremise4StillMustBeSuppliedExternallyAfterRule828IsFalse' DASHI/Foundations/Wette1969Rule828To9324x25DerivationExact.agda

grep -q 'firstThreeCriticalPremisesCanComeFromCertifiedProducerTracesIsTrue' DASHI/Foundations/Wette1969CriticalPremiseLocalDerivationExact.agda
grep -q 'completeProducer828CriticalTracesNowComposeDependentlyIsTrue' DASHI/Foundations/Wette1969CriticalPremiseLocalDerivationExact.agda
grep -q 'firstThreeCriticalPremisesMustBeInitialContextMembershipFactsIsFalse' DASHI/Foundations/Wette1969CriticalPremiseLocalDerivationExact.agda

grep -q 'premise1CanBeGeneratedByCertifiedRule915IsTrue' DASHI/Foundations/Wette1969CriticalPremiseConcreteProducerChainExact.agda
grep -q 'premise2CanBeGeneratedByCertifiedRule832IsTrue' DASHI/Foundations/Wette1969CriticalPremiseConcreteProducerChainExact.agda
grep -q 'premise3CanBeGeneratedByCertifiedRule8112IsTrue' DASHI/Foundations/Wette1969CriticalPremiseConcreteProducerChainExact.agda
grep -q 'firstThreeProducerRulesComposeIntoCriticalChainIsTrue' DASHI/Foundations/Wette1969CriticalPremiseConcreteProducerChainExact.agda

grep -q 'sourceQuantifierCaptureCriterionNowTypedIsTrue' DASHI/Foundations/Wette1969QuantifierCaptureSafetyExact.agda
grep -q 'exactRecursorBinderTargetParserNowRecoveredIsTrue' DASHI/Foundations/Wette1969RecursorBindingScopeExact.agda

grep -q 'premise4HasIndependentPairedSubstituendAndReplacementIsTrue' DASHI/Foundations/Wette1969Rule9324x25PremiseTemplateExact.agda
grep -q 'computationalCertificateIsAlreadyHistoricalDerivabilityProofIsFalse' DASHI/Foundations/Wette1969Rule9324x25ComputationalSideConditionsExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Core/ProofCarryingRuleApplicationExact.agda \
  DASHI/Foundations/Wette1969Rule915PredicateProducerExact.agda \
  DASHI/Foundations/Wette1969Rule83TupleDerivationExact.agda \
  DASHI/Foundations/Wette1969Rule8112FreshnessDerivationExact.agda \
  DASHI/Foundations/Wette1969DerivationClosureExact.agda \
  DASHI/Foundations/Wette1969ObjectVariableMarkWordsExact.agda \
  DASHI/Foundations/Wette1969QuantifierCaptureSafetyExact.agda \
  DASHI/Foundations/Wette1969RecursorBindingScopeExact.agda \
  DASHI/Foundations/Wette1969DependentTwoStageSubstitutionExact.agda \
  DASHI/Foundations/Wette1969Rule9324x25PremiseTemplateExact.agda \
  DASHI/Foundations/Wette1969Rule828To9324x25DerivationExact.agda \
  DASHI/Foundations/Wette1969CriticalPremiseLocalDerivationExact.agda \
  DASHI/Foundations/Wette1969CriticalPremiseConcreteProducerChainExact.agda
