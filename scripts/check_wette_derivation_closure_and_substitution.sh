#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Core/ProofCarryingRuleApplicationExact.agda
  DASHI/Foundations/Wette1969FiniteDerivationContextExact.agda
  DASHI/Foundations/Wette1969DerivationClosureExact.agda
  DASHI/Foundations/Wette1969Rule915PredicateProducerExact.agda
  DASHI/Foundations/Wette1969Rule915ObligationSubgraphsExact.agda
  DASHI/Foundations/Wette1969Rule915CertifiedObligationApplicationExact.agda
  DASHI/Foundations/Wette1969Rule915ObligationProducerChainExact.agda
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
  DASHI/Foundations/Wette1969RecursiveDefinitionSpineExact.agda
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

grep -q 'firstSevenPremiseBodiesNowLiteralSourceConstructorsIsTrue' DASHI/Foundations/Wette1969Rule915PredicateProducerExact.agda
grep -q 'remainingTwentyLPremisesStillExplicitTranscriptionObligationsIsTrue' DASHI/Foundations/Wette1969Rule915PredicateProducerExact.agda

grep -q 'premises10To15OwnedByOneSharedEvidenceObjectIsTrue' DASHI/Foundations/Wette1969Rule915ObligationSubgraphsExact.agda
grep -q 'inductionAndIndependenceBranchesRemainDistinctIsTrue' DASHI/Foundations/Wette1969Rule915ObligationSubgraphsExact.agda
grep -q 'proofPackagingAlreadyRecoversAllLiteralLPremiseBodiesIsFalse' DASHI/Foundations/Wette1969Rule915ObligationSubgraphsExact.agda

grep -q 'factoredObligationEvidenceNowCertifiesRule915IsTrue' DASHI/Foundations/Wette1969Rule915CertifiedObligationApplicationExact.agda
grep -q 'shared1015EvidenceIsNotDuplicatedAtApplicationBoundaryIsTrue' DASHI/Foundations/Wette1969Rule915CertifiedObligationApplicationExact.agda

grep -q 'shared1015ProducedOnceAndTransportedToBothBranchesIsTrue' DASHI/Foundations/Wette1969Rule915ObligationProducerChainExact.agda
grep -q 'completeObligationProducerChainCanCertifyRule915IsTrue' DASHI/Foundations/Wette1969Rule915ObligationProducerChainExact.agda
grep -q 'producerChainAutomaticallyConstructsAllUnderlyingHistoricalRulesIsFalse' DASHI/Foundations/Wette1969Rule915ObligationProducerChainExact.agda

grep -q 'rules831And832NowLiteralHistoricalBodiesIsTrue' DASHI/Foundations/Wette1969Rule83TupleDerivationExact.agda
grep -q 'rules8112And8113NowLiteralHistoricalBodiesIsTrue' DASHI/Foundations/Wette1969Rule8112FreshnessDerivationExact.agda

grep -q 'variableAndPredicateMarkBaseRulesRecoveredIsTrue' DASHI/Foundations/Wette1969SubstitutionRuleSpineExact.agda
grep -q 'quantifierAndRecursorBinderCongruenceRulesRecoveredIsTrue' DASHI/Foundations/Wette1969SubstitutionRuleSpineExact.agda
grep -q 'recoveredRuleSpineIsAlreadyTotalDecisionProcedureIsFalse' DASHI/Foundations/Wette1969SubstitutionRuleSpineExact.agda

grep -q 'historicalIIJudgementsNowComposeByCertified82RulesIsTrue' DASHI/Foundations/Wette1969CertifiedSubstitutionDerivationExact.agda
grep -q 'recursorSubstitutionNowHasComposableHistoricalDerivationConstructorIsTrue' DASHI/Foundations/Wette1969CertifiedSubstitutionDerivationExact.agda
grep -q 'compositionalDerivationIsAlreadyTotalSubstitutionDecisionProcedureIsFalse' DASHI/Foundations/Wette1969CertifiedSubstitutionDerivationExact.agda

grep -q 'firstIICanBeGeneratedByHistorical82DerivationIsTrue' DASHI/Foundations/Wette1969CertifiedTwoStageIIDerivationExact.agda
grep -q 'secondIIStartsAtActualFirstDerivationTargetIsTrue' DASHI/Foundations/Wette1969CertifiedTwoStageIIDerivationExact.agda
grep -q 'pairedIINoLongerRequiresInitialContextMembershipIsTrue' DASHI/Foundations/Wette1969CertifiedTwoStageIIDerivationExact.agda

grep -q 'allFourCriticalPremisesCanBeGeneratedByCertifiedLocalTracesIsTrue' DASHI/Foundations/Wette1969FullyGeneratedCriticalApplicationExact.agda
grep -q 'fullyGeneratedLocalTraceStartsFromEmptyContextWithoutAnySideConditionsIsFalse' DASHI/Foundations/Wette1969FullyGeneratedCriticalApplicationExact.agda

grep -q 'factored915ObligationsNowFeedCriticalRecursiveApplicationIsTrue' DASHI/Foundations/Wette1969RecursiveDefinitionSpineExact.agda
grep -q 'rule915PredicateOutputFeedsPremise1WithoutExternalMembershipIsTrue' DASHI/Foundations/Wette1969RecursiveDefinitionSpineExact.agda
grep -q 'tupleFreshnessAndPairedIIFollowAtActualReachedStatesIsTrue' DASHI/Foundations/Wette1969RecursiveDefinitionSpineExact.agda
grep -q 'recursiveSpineIsAlreadyClosedFromEmptyContextIsFalse' DASHI/Foundations/Wette1969RecursiveDefinitionSpineExact.agda

grep -q 'sourceQuantifierCaptureCriterionNowTypedIsTrue' DASHI/Foundations/Wette1969QuantifierCaptureSafetyExact.agda
grep -q 'exactRecursorBinderTargetParserNowRecoveredIsTrue' DASHI/Foundations/Wette1969RecursorBindingScopeExact.agda
grep -q 'premise4HasIndependentPairedSubstituendAndReplacementIsTrue' DASHI/Foundations/Wette1969Rule9324x25PremiseTemplateExact.agda

grep -q 'DOI: 10.1007/978-3-642-86745-3_9' DASHI/Foundations/Wette1969Rule915PredicateProducerExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Core/ProofCarryingRuleApplicationExact.agda \
  DASHI/Foundations/Wette1969Rule915PredicateProducerExact.agda \
  DASHI/Foundations/Wette1969Rule915ObligationSubgraphsExact.agda \
  DASHI/Foundations/Wette1969Rule915CertifiedObligationApplicationExact.agda \
  DASHI/Foundations/Wette1969Rule915ObligationProducerChainExact.agda \
  DASHI/Foundations/Wette1969Rule83TupleDerivationExact.agda \
  DASHI/Foundations/Wette1969Rule8112FreshnessDerivationExact.agda \
  DASHI/Foundations/Wette1969DerivationClosureExact.agda \
  DASHI/Foundations/Wette1969QuantifierCaptureSafetyExact.agda \
  DASHI/Foundations/Wette1969RecursorBindingScopeExact.agda \
  DASHI/Foundations/Wette1969SubstitutionRuleSpineExact.agda \
  DASHI/Foundations/Wette1969CertifiedSubstitutionDerivationExact.agda \
  DASHI/Foundations/Wette1969DependentTwoStageSubstitutionExact.agda \
  DASHI/Foundations/Wette1969CertifiedTwoStageIIDerivationExact.agda \
  DASHI/Foundations/Wette1969Rule9324x25PremiseTemplateExact.agda \
  DASHI/Foundations/Wette1969Rule828To9324x25DerivationExact.agda \
  DASHI/Foundations/Wette1969FullyGeneratedCriticalApplicationExact.agda \
  DASHI/Foundations/Wette1969RecursiveDefinitionSpineExact.agda
