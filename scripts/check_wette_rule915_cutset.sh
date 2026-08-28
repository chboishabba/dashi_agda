#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Foundations/Wette1969Rule34ObjectProducerExact.agda
  DASHI/Foundations/Wette1969Rule8117PredicateMarkFreshnessExact.agda
  DASHI/Foundations/Wette1969Rule915MajorObligationTemplatesExact.agda
  DASHI/Foundations/Wette1969Rule915LaterPremiseTemplatesExact.agda
  DASHI/Foundations/Wette1969Rule915ParameterCoherenceExact.agda
  DASHI/Foundations/Wette1969Rule915DecidableScaffoldCutsetExact.agda
  DASHI/Foundations/Wette1969Rule915TwoProofCutsetExact.agda
  DASHI/Foundations/Wette1969Rule915CoherentTwoProofApplicationExact.agda
  DASHI/Foundations/Wette1969Rule915ObligationSubgraphsExact.agda
  DASHI/Foundations/Wette1969Rule915CertifiedObligationApplicationExact.agda
  DASHI/Foundations/Wette1969Rule915ObligationProducerChainExact.agda
  DASHI/Foundations/Wette1969InductionBranchPremise8ProducerExact.agda
  DASHI/Foundations/Wette1969Rule915Premise1921DerivationExact.agda
  DASHI/Foundations/Wette1969Rule915Premise2425DerivationExact.agda
  DASHI/Foundations/Wette1969IndependenceBranch2425ProducerExact.agda
  DASHI/Foundations/Wette1969IndependenceBranchGeneratedCoreExact.agda
  DASHI/Foundations/Wette1969RecursiveDefinitionSpineExact.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required Wette 9.1.5 cutset source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q 'rule4NowProducesCanonicalPredicateMarkHistoricallyIsTrue' DASHI/Foundations/Wette1969Rule34ObjectProducerExact.agda
grep -q 'sameArityDistinctIndexMarksGainHistoricalFreshnessIsTrue' DASHI/Foundations/Wette1969Rule8117PredicateMarkFreshnessExact.agda

grep -q 'allTwentyLaterSlotsNowHaveFixedHistoricalJudgementKindsIsTrue' DASHI/Foundations/Wette1969Rule915LaterPremiseTemplatesExact.agda
grep -q 'premises24And25NowLiteralPairedIITemplatesIsTrue' DASHI/Foundations/Wette1969Rule915LaterPremiseTemplatesExact.agda
grep -q 'completeTypedTranscriptionHasNoArbitraryFormulaSlotsIsTrue' DASHI/Foundations/Wette1969Rule915LaterPremiseTemplatesExact.agda
grep -q 'denseCompoundWordParametersAreAlreadyCharacterPerfectSourceTranscriptionIsFalse' DASHI/Foundations/Wette1969Rule915LaterPremiseTemplatesExact.agda

grep -q 'stagedPremiseBlocksNowRequireSameObjectWeldIsTrue' DASHI/Foundations/Wette1969Rule915ParameterCoherenceExact.agda
grep -q 'roleCompatibilityAloneIsEnoughForHistoricalIdentityIsFalse' DASHI/Foundations/Wette1969Rule915ParameterCoherenceExact.agda

grep -q 'twentyLCausedPremisesFactorAsEighteenScaffoldPlusTwoProofsIsTrue' DASHI/Foundations/Wette1969Rule915DecidableScaffoldCutsetExact.agda
grep -q 'premise18And27AreOnlyMajorProofSlotsInLBlockIsTrue' DASHI/Foundations/Wette1969Rule915DecidableScaffoldCutsetExact.agda
grep -q 'sourceDecidabilityClaimAlreadyEqualsImplementedAgdaDeciderIsFalse' DASHI/Foundations/Wette1969Rule915DecidableScaffoldCutsetExact.agda

grep -q 'rule915EvidenceFactorsIntoScaffoldPlusTwoMajorProofsIsTrue' DASHI/Foundations/Wette1969Rule915TwoProofCutsetExact.agda
grep -q 'premise18IsExplicitPredecessorInductionProofSocketIsTrue' DASHI/Foundations/Wette1969Rule915TwoProofCutsetExact.agda
grep -q 'premise27IsExplicitDefiniensIndependenceProofSocketIsTrue' DASHI/Foundations/Wette1969Rule915TwoProofCutsetExact.agda
grep -q 'twoProofCutsetAlreadyDischargesEitherMajorProofIsFalse' DASHI/Foundations/Wette1969Rule915TwoProofCutsetExact.agda

grep -q 'twoProofCutsetNowHasSameObjectParameterWeldIsTrue' DASHI/Foundations/Wette1969Rule915CoherentTwoProofApplicationExact.agda

grep -q 'premise8NoLongerNeedsExternalMarkFormationEvidenceIsTrue' DASHI/Foundations/Wette1969InductionBranchPremise8ProducerExact.agda
grep -q 'premises19And20GeneratedByHistoricalRule4IsTrue' DASHI/Foundations/Wette1969Rule915Premise1921DerivationExact.agda
grep -q 'premise21GeneratedByHistoricalRule8117IsTrue' DASHI/Foundations/Wette1969Rule915Premise1921DerivationExact.agda
grep -q 'premise24CanBeGeneratedByHistorical82CompositionIsTrue' DASHI/Foundations/Wette1969Rule915Premise2425DerivationExact.agda
grep -q 'premise25CanBeGeneratedByHistorical82CompositionIsTrue' DASHI/Foundations/Wette1969Rule915Premise2425DerivationExact.agda
grep -q 'independencePremises24And25NoLongerExternalEvidenceIsTrue' DASHI/Foundations/Wette1969IndependenceBranch2425ProducerExact.agda
grep -q 'independenceExternalResidueReducedTo22_23_26_27PlusSharedCoreIsTrue' DASHI/Foundations/Wette1969IndependenceBranchGeneratedCoreExact.agda

grep -q 'factored915ObligationsNowFeedCriticalRecursiveApplicationIsTrue' DASHI/Foundations/Wette1969RecursiveDefinitionSpineExact.agda
grep -q 'recursiveSpineKeepsExplicitTraceIdentityReceiptIsTrue' DASHI/Foundations/Wette1969RecursiveDefinitionSpineExact.agda

grep -q 'DOI 10.1007/978-3-642-86745-3_9' DASHI/Foundations/Wette1969Rule915LaterPremiseTemplatesExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Foundations/Wette1969Rule34ObjectProducerExact.agda \
  DASHI/Foundations/Wette1969Rule8117PredicateMarkFreshnessExact.agda \
  DASHI/Foundations/Wette1969Rule915MajorObligationTemplatesExact.agda \
  DASHI/Foundations/Wette1969Rule915LaterPremiseTemplatesExact.agda \
  DASHI/Foundations/Wette1969Rule915ParameterCoherenceExact.agda \
  DASHI/Foundations/Wette1969Rule915DecidableScaffoldCutsetExact.agda \
  DASHI/Foundations/Wette1969Rule915TwoProofCutsetExact.agda \
  DASHI/Foundations/Wette1969Rule915CoherentTwoProofApplicationExact.agda \
  DASHI/Foundations/Wette1969Rule915ObligationSubgraphsExact.agda \
  DASHI/Foundations/Wette1969Rule915CertifiedObligationApplicationExact.agda \
  DASHI/Foundations/Wette1969Rule915ObligationProducerChainExact.agda \
  DASHI/Foundations/Wette1969InductionBranchPremise8ProducerExact.agda \
  DASHI/Foundations/Wette1969Rule915Premise1921DerivationExact.agda \
  DASHI/Foundations/Wette1969Rule915Premise2425DerivationExact.agda \
  DASHI/Foundations/Wette1969IndependenceBranch2425ProducerExact.agda \
  DASHI/Foundations/Wette1969IndependenceBranchGeneratedCoreExact.agda \
  DASHI/Foundations/Wette1969RecursiveDefinitionSpineExact.agda
