#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Foundations/Wette1969Rule93ImplicationFamilyExact.agda
  DASHI/Foundations/Wette1969Rule93CompleteCandidateAuditExact.agda
  DASHI/Foundations/Wette1969Rule939ImplicationIntroductionExact.agda
  DASHI/Foundations/Wette1969Rule9323InductionExact.agda
  DASHI/Foundations/Wette1969Rule915MajorPDFSourceAuditExact.agda
  DASHI/Foundations/Wette1969Rule915Premise18ImplicationSpineExact.agda
  DASHI/Foundations/Wette1969Rule915Premise18CoreLeafClosureExact.agda
  DASHI/Foundations/Wette1969Rule915Premise18Rule9323ResolutionExact.agda
  DASHI/Foundations/Wette/Everything.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required Wette premise-18 source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q 'allThirtyPrintedCandidatesHaveExplicitConstructorsIsTrue' DASHI/Foundations/Wette1969Rule93CompleteCandidateAuditExact.agda
grep -q 'allThirtyPrintedPremiseCountsRecordedIsTrue' DASHI/Foundations/Wette1969Rule93CompleteCandidateAuditExact.agda
grep -q 'rule939IsUniqueExplicitDirectImplicationBuilderInThisClassificationIsTrue' DASHI/Foundations/Wette1969Rule93CompleteCandidateAuditExact.agda
grep -q 'non939CandidatesAreRejectedWithoutUnificationIsFalse' DASHI/Foundations/Wette1969Rule93CompleteCandidateAuditExact.agda

grep -q 'rule939BodyTranscribedFromPrintedP145IsTrue' DASHI/Foundations/Wette1969Rule939ImplicationIntroductionExact.agda
grep -q 'rule9323BodyTranscribedFromPrintedP145IsTrue' DASHI/Foundations/Wette1969Rule9323InductionExact.agda
grep -q 'rule9323AutomaticallyProvesArbitraryPredecessorInductionIsFalse' DASHI/Foundations/Wette1969Rule9323InductionExact.agda

grep -q 'p145OuterConsequentRecoveredAsTwoNestedImplicationsIsTrue' DASHI/Foundations/Wette1969Rule915Premise18ImplicationSpineExact.agda
grep -q 'p145SpineRecoveryByItselfProvesCoreLeafIsFalse' DASHI/Foundations/Wette1969Rule915Premise18ImplicationSpineExact.agda

grep -q 'certifiedCoreLeafClosesPremise18IsTrue' DASHI/Foundations/Wette1969Rule915Premise18CoreLeafClosureExact.agda
grep -q 'closureUsesExactlyTwoExplicitRule939StepsIsTrue' DASHI/Foundations/Wette1969Rule915Premise18CoreLeafClosureExact.agda
grep -q 'syntacticScaffoldAloneManufacturesCoreLeafIsFalse' DASHI/Foundations/Wette1969Rule915Premise18CoreLeafClosureExact.agda

grep -q 'matched9323PremisesProduceCoreLeafIsTrue' DASHI/Foundations/Wette1969Rule915Premise18Rule9323ResolutionExact.agda
grep -q 'coreLeafThenClosesD18ByTwoRule939StepsIsTrue' DASHI/Foundations/Wette1969Rule915Premise18Rule9323ResolutionExact.agda
grep -q 'genericScaffoldAutomaticallySuppliesFive9323PremisesIsFalse' DASHI/Foundations/Wette1969Rule915Premise18Rule9323ResolutionExact.agda
grep -q 'arbitraryRelationRIsAutomaticallyHandledBy9323IsFalse' DASHI/Foundations/Wette1969Rule915Premise18Rule9323ResolutionExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Foundations/Wette1969Rule93ImplicationFamilyExact.agda \
  DASHI/Foundations/Wette1969Rule93CompleteCandidateAuditExact.agda \
  DASHI/Foundations/Wette1969Rule939ImplicationIntroductionExact.agda \
  DASHI/Foundations/Wette1969Rule9323InductionExact.agda \
  DASHI/Foundations/Wette1969Rule915MajorPDFSourceAuditExact.agda \
  DASHI/Foundations/Wette1969Rule915Premise18ImplicationSpineExact.agda \
  DASHI/Foundations/Wette1969Rule915Premise18CoreLeafClosureExact.agda \
  DASHI/Foundations/Wette1969Rule915Premise18Rule9323ResolutionExact.agda \
  DASHI/Foundations/Wette/Everything.agda
