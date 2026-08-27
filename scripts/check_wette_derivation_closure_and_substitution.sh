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
  DASHI/Foundations/Wette1969ObjectVariableMarkWordsExact.agda
  DASHI/Foundations/Wette1969QuantifierCaptureSafetyExact.agda
  DASHI/Foundations/Wette1969RecursorBindingScopeExact.agda
  DASHI/Foundations/Wette1969SubstitutionRuleSpineExact.agda
  DASHI/Foundations/Wette1969Rule8211RecursorSubstitutionExact.agda
  DASHI/Foundations/Wette1969CertifiedSubstitutionDerivationExact.agda
  DASHI/Foundations/Wette1969DependentTwoStageSubstitutionExact.agda
  DASHI/Foundations/Wette1969CertifiedTwoStageIIDerivationExact.agda
  DASHI/Foundations/Wette1969Rule9324x25PremiseTemplateExact.agda
  DASHI/Foundations/Wette1969Rule9324x25ComputationalSideConditionsExact.agda
  DASHI/Foundations/Wette1969Rule828To9324x25DerivationExact.agda
  DASHI/Foundations/Wette1969CriticalPremiseLocalDerivationExact.agda
  DASHI/Foundations/Wette1969CriticalPremiseConcreteProducerChainExact.agda
  DASHI/Foundations/Wette1969FullyGeneratedCriticalApplicationExact.agda
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

grep -q 'rule915AddressCountAndPredicateOutputNowTypedIsTrue' DASHI/Foundations/Wette1969Rule915PredicateProducerExact.agda
grep -q 'firstSevenPremiseBodiesNowLiteralSourceConstructorsIsTrue' DASHI/Foundations/Wette1969Rule915PredicateProducerExact.agda
grep -q 'modifiedPremise6UsesP193NoPredicateQuantificationConditionIsTrue' DASHI/Foundations/Wette1969Rule915PredicateProducerExact.agda
grep -q 'remainingTwentyLPremisesStillExplicitTranscriptionObligationsIsTrue' DASHI/Foundations/Wette1969Rule915PredicateProducerExact.agda
grep -q 'allTwentySevenPremiseBodiesNowLiteralOCRPerfectIsFalse' DASHI/Foundations/Wette1969Rule915PredicateProducerExact.agda

grep -q 'rules831And832NowLiteralHistoricalBodiesIsTrue' DASHI/Foundations/Wette1969Rule83TupleDerivationExact.agda
grep -q 'rules8112And8113NowLiteralHistoricalBodiesIsTrue' DASHI/Foundations/Wette1969Rule8112FreshnessDerivationExact.agda

grep -q 'variableAndPredicateMarkBaseRulesRecoveredIsTrue' DASHI/Foundations/Wette1969SubstitutionRuleSpineExact.agda
grep -q 'unaryAndBinaryCongruenceRulesRecoveredIsTrue' DASHI/Foundations/Wette1969SubstitutionRuleSpineExact.agda
grep -q 'quantifierAndRecursorBinderCongruenceRulesRecoveredIsTrue' DASHI/Foundations/Wette1969SubstitutionRuleSpineExact.agda
grep -q 'recoveredRuleSpineIsAlreadyTotalDecisionProcedureIsFalse' DASHI/Foundations/Wette1969SubstitutionRuleSpineExact.agda

grep -q 'substitutionSpineOwnsLiteralRule8211IsTrue' DASHI/Foundations/Wette1969Rule8211RecursorSubstitutionExact.agda
grep -q 'certifiedBodySubstitutionCanGenerateRecursorSubstitutionIsTrue' DASHI/Foundations/Wette1969Rule8211RecursorSubstitutionExact.agda

grep -q 'historicalIIJudgementsNowComposeByCertified82RulesIsTrue' DASHI/Foundations/Wette1969CertifiedSubstitutionDerivationExact.agda
grep -q 'binarySubderivationsSequenceAtActualReachedContextsIsTrue' DASHI/Foundations/Wette1969CertifiedSubstitutionDerivationExact.agda
grep -q 'binderFreshnessTransportedToBodyDerivationTargetIsTrue' DASHI/Foundations/Wette1969CertifiedSubstitutionDerivationExact.agda
grep -q 'recursorSubstitutionNowHasComposableHistoricalDerivationConstructorIsTrue' DASHI/Foundations/Wette1969CertifiedSubstitutionDerivationExact.agda
grep -q 'compositionalDerivationIsAlreadyTotalSubstitutionDecisionProcedureIsFalse' DASHI/Foundations/Wette1969CertifiedSubstitutionDerivationExact.agda

grep -q 'secondStageSafetyIndexedByActualIntermediateIsTrue' DASHI/Foundations/Wette1969DependentTwoStageSubstitutionExact.agda
grep -q 'pairedFourPlaceIIJudgementNowReproducedIsTrue' DASHI/Foundations/Wette1969DependentTwoStageSubstitutionExact.agda

grep -q 'firstIICanBeGeneratedByHistorical82DerivationIsTrue' DASHI/Foundations/Wette1969CertifiedTwoStageIIDerivationExact.agda
grep -q 'secondIIStartsAtActualFirstDerivationTargetIsTrue' DASHI/Foundations/Wette1969CertifiedTwoStageIIDerivationExact.agda
grep -q 'rule828CanConsumeGeneratedSequentialIIsIsTrue' DASHI/Foundations/Wette1969CertifiedTwoStageIIDerivationExact.agda
grep -q 'pairedIINoLongerRequiresInitialContextMembershipIsTrue' DASHI/Foundations/Wette1969CertifiedTwoStageIIDerivationExact.agda

grep -q 'rule828ConclusionDefinitionallyMatchesCriticalPremise4IsTrue' DASHI/Foundations/Wette1969Rule828To9324x25DerivationExact.agda
grep -q 'criticalPremise4StillMustBeSuppliedExternallyAfterRule828IsFalse' DASHI/Foundations/Wette1969Rule828To9324x25DerivationExact.agda

grep -q 'firstThreeCriticalPremisesCanComeFromCertifiedProducerTracesIsTrue' DASHI/Foundations/Wette1969CriticalPremiseLocalDerivationExact.agda
grep -q 'firstThreeCriticalPremisesMustBeInitialContextMembershipFactsIsFalse' DASHI/Foundations/Wette1969CriticalPremiseLocalDerivationExact.agda

grep -q 'premise1CanBeGeneratedByCertifiedRule915IsTrue' DASHI/Foundations/Wette1969CriticalPremiseConcreteProducerChainExact.agda
grep -q 'premise2CanBeGeneratedByCertifiedRule832IsTrue' DASHI/Foundations/Wette1969CriticalPremiseConcreteProducerChainExact.agda
grep -q 'premise3CanBeGeneratedByCertifiedRule8112IsTrue' DASHI/Foundations/Wette1969CriticalPremiseConcreteProducerChainExact.agda

grep -q 'allFourCriticalPremisesCanBeGeneratedByCertifiedLocalTracesIsTrue' DASHI/Foundations/Wette1969FullyGeneratedCriticalApplicationExact.agda
grep -q 'sequentialIIPremisesNoLongerNeedInitialMembershipIsTrue' DASHI/Foundations/Wette1969FullyGeneratedCriticalApplicationExact.agda
grep -q 'rules9324And9325CanConsumeFullyGeneratedPremiseContextsIsTrue' DASHI/Foundations/Wette1969FullyGeneratedCriticalApplicationExact.agda
grep -q 'fullyGeneratedLocalTraceStartsFromEmptyContextWithoutAnySideConditionsIsFalse' DASHI/Foundations/Wette1969FullyGeneratedCriticalApplicationExact.agda

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
  DASHI/Foundations/Wette1969SubstitutionRuleSpineExact.agda \
  DASHI/Foundations/Wette1969Rule8211RecursorSubstitutionExact.agda \
  DASHI/Foundations/Wette1969CertifiedSubstitutionDerivationExact.agda \
  DASHI/Foundations/Wette1969DependentTwoStageSubstitutionExact.agda \
  DASHI/Foundations/Wette1969CertifiedTwoStageIIDerivationExact.agda \
  DASHI/Foundations/Wette1969Rule9324x25PremiseTemplateExact.agda \
  DASHI/Foundations/Wette1969Rule828To9324x25DerivationExact.agda \
  DASHI/Foundations/Wette1969CriticalPremiseLocalDerivationExact.agda \
  DASHI/Foundations/Wette1969CriticalPremiseConcreteProducerChainExact.agda \
  DASHI/Foundations/Wette1969FullyGeneratedCriticalApplicationExact.agda
