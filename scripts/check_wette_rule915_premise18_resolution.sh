#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Foundations/Wette1969Rule915CanonicalP145PremisesExact.agda
  DASHI/Foundations/Wette1969Rule915CanonicalP145TypedWeldExact.agda
  DASHI/Foundations/Wette1969Rule93ImplicationFamilyExact.agda
  DASHI/Foundations/Wette1969Rule93CompleteCandidateAuditExact.agda
  DASHI/Foundations/Wette1969Rule935ConjunctionExact.agda
  DASHI/Foundations/Wette1969Rule939ImplicationIntroductionExact.agda
  DASHI/Foundations/Wette1969Rule9323InductionExact.agda
  DASHI/Foundations/Wette1969Rule915MajorPDFSourceAuditExact.agda
  DASHI/Foundations/Wette1969Rule915Premise18ImplicationSpineExact.agda
  DASHI/Foundations/Wette1969Rule915Premise18CoreLeafClosureExact.agda
  DASHI/Foundations/Wette1969Rule915Premise18Rule9323ResolutionExact.agda
  DASHI/Foundations/Wette1969Rule915Premise27DirectionalClosureExact.agda
  DASHI/Foundations/Wette/Everything.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required Wette 9.1.5 closure source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q 'allTwentySevenP145PremisesNowOneConcreteTypedVectorIsTrue' DASHI/Foundations/Wette1969Rule915CanonicalP145PremisesExact.agda
grep -q 'premise18DenseWordNoLongerOpaqueInCanonicalP145SurfaceIsTrue' DASHI/Foundations/Wette1969Rule915CanonicalP145PremisesExact.agda
grep -q 'premise27DenseWordNoLongerOpaqueInCanonicalP145SurfaceIsTrue' DASHI/Foundations/Wette1969Rule915CanonicalP145PremisesExact.agda
grep -q 'thisModuleClaimsDerivabilityOfAnyPremiseIsFalse' DASHI/Foundations/Wette1969Rule915CanonicalP145PremisesExact.agda

grep -q 'allTwentySevenExistingTypedSlotsPointwiseMatchP145IsTrue' DASHI/Foundations/Wette1969Rule915CanonicalP145TypedWeldExact.agda
grep -q 'premise18And27NoLongerNeedOpaqueWordParametersForCanonicalP145InstanceIsTrue' DASHI/Foundations/Wette1969Rule915CanonicalP145TypedWeldExact.agda
grep -q 'bridgeIntroducesParallelRule915SemanticsIsFalse' DASHI/Foundations/Wette1969Rule915CanonicalP145TypedWeldExact.agda

grep -q 'exhaustiveNamedThirtyCandidateAuditNowExistsIsTrue' DASHI/Foundations/Wette1969Rule93ImplicationFamilyExact.agda
grep -q 'allThirtyPrintedCandidatesHaveExplicitConstructorsIsTrue' DASHI/Foundations/Wette1969Rule93CompleteCandidateAuditExact.agda
grep -q 'allThirtyPrintedPremiseCountsRecordedIsTrue' DASHI/Foundations/Wette1969Rule93CompleteCandidateAuditExact.agda
grep -q 'allThirtyCandidatesHaveSourceRoleClassificationIsTrue' DASHI/Foundations/Wette1969Rule93CompleteCandidateAuditExact.agda
grep -q 'rule939IsUniqueExplicitDirectImplicationBuilderInThisClassificationIsTrue' DASHI/Foundations/Wette1969Rule93CompleteCandidateAuditExact.agda
grep -q 'non939CandidatesAreRejectedWithoutUnificationIsFalse' DASHI/Foundations/Wette1969Rule93CompleteCandidateAuditExact.agda

grep -q 'rule935BodyTranscribedFromPrintedP145IsTrue' DASHI/Foundations/Wette1969Rule935ConjunctionExact.agda
grep -q 'rule939BodyTranscribedFromPrintedP145IsTrue' DASHI/Foundations/Wette1969Rule939ImplicationIntroductionExact.agda
grep -q 'rule9323BodyTranscribedFromPrintedP145IsTrue' DASHI/Foundations/Wette1969Rule9323InductionExact.agda
grep -q 'rule9323AutomaticallyProvesArbitraryPredecessorInductionIsFalse' DASHI/Foundations/Wette1969Rule9323InductionExact.agda

grep -q 'p145PrintsTheComplete931Through9330SurfaceIsTrue' DASHI/Foundations/Wette1969Rule915MajorPDFSourceAuditExact.agda
grep -q 'p158ErratumIdentifiesNewPremise18TerminalRuleIsFalse' DASHI/Foundations/Wette1969Rule915MajorPDFSourceAuditExact.agda
grep -q 'implicationProducingRulesMustBeSoughtOnP145NotInventedFromP158ErratumIsTrue' DASHI/Foundations/Wette1969Rule915MajorPDFSourceAuditExact.agda

grep -q 'p145OuterConsequentRecoveredAsTwoNestedImplicationsIsTrue' DASHI/Foundations/Wette1969Rule915Premise18ImplicationSpineExact.agda
grep -q 'p145SpineRecoveryByItselfProvesCoreLeafIsFalse' DASHI/Foundations/Wette1969Rule915Premise18ImplicationSpineExact.agda

grep -q 'certifiedCoreLeafClosesPremise18IsTrue' DASHI/Foundations/Wette1969Rule915Premise18CoreLeafClosureExact.agda
grep -q 'closureUsesExactlyTwoExplicitRule939StepsIsTrue' DASHI/Foundations/Wette1969Rule915Premise18CoreLeafClosureExact.agda
grep -q 'syntacticScaffoldAloneManufacturesCoreLeafIsFalse' DASHI/Foundations/Wette1969Rule915Premise18CoreLeafClosureExact.agda

grep -q 'matched9323PremisesProduceCoreLeafIsTrue' DASHI/Foundations/Wette1969Rule915Premise18Rule9323ResolutionExact.agda
grep -q 'coreLeafThenClosesD18ByTwoRule939StepsIsTrue' DASHI/Foundations/Wette1969Rule915Premise18Rule9323ResolutionExact.agda
grep -q 'genericScaffoldAutomaticallySuppliesFive9323PremisesIsFalse' DASHI/Foundations/Wette1969Rule915Premise18Rule9323ResolutionExact.agda
grep -q 'arbitraryRelationRIsAutomaticallyHandledBy9323IsFalse' DASHI/Foundations/Wette1969Rule915Premise18Rule9323ResolutionExact.agda

grep -q 'exactP145Premise27ReducedToTwoDirectionalLeavesIsTrue' DASHI/Foundations/Wette1969Rule915Premise27DirectionalClosureExact.agda
grep -q 'closureUsesOneRule935AndTwoRule939StepsIsTrue' DASHI/Foundations/Wette1969Rule915Premise27DirectionalClosureExact.agda
grep -q 'directionalSuffixIsProofCarryingHistoricalTraceIsTrue' DASHI/Foundations/Wette1969Rule915Premise27DirectionalClosureExact.agda
grep -q 'closureManufacturesEitherDirectionalLeafIsFalse' DASHI/Foundations/Wette1969Rule915Premise27DirectionalClosureExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Foundations/Wette1969Rule915CanonicalP145PremisesExact.agda \
  DASHI/Foundations/Wette1969Rule915CanonicalP145TypedWeldExact.agda \
  DASHI/Foundations/Wette1969Rule93ImplicationFamilyExact.agda \
  DASHI/Foundations/Wette1969Rule93CompleteCandidateAuditExact.agda \
  DASHI/Foundations/Wette1969Rule935ConjunctionExact.agda \
  DASHI/Foundations/Wette1969Rule939ImplicationIntroductionExact.agda \
  DASHI/Foundations/Wette1969Rule9323InductionExact.agda \
  DASHI/Foundations/Wette1969Rule915MajorPDFSourceAuditExact.agda \
  DASHI/Foundations/Wette1969Rule915Premise18ImplicationSpineExact.agda \
  DASHI/Foundations/Wette1969Rule915Premise18CoreLeafClosureExact.agda \
  DASHI/Foundations/Wette1969Rule915Premise18Rule9323ResolutionExact.agda \
  DASHI/Foundations/Wette1969Rule915Premise27DirectionalClosureExact.agda \
  DASHI/Foundations/Wette/Everything.agda
