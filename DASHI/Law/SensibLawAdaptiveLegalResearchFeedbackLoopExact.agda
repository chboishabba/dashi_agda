module DASHI.Law.SensibLawAdaptiveLegalResearchFeedbackLoopExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Assessment
import DASHI.Cognition.PNF.SensibLawLegalGraphRefinementReopeningExact as Refinement
import DASHI.Cognition.PNF.SensibLawLegalObserverResidualRefinementBidiExact as Residual
import DASHI.Cognition.PNF.SensibLawClimateDutyRouteSearchExact as Climate

------------------------------------------------------------------------
-- ADAPTIVE LEGAL RESEARCH FEEDBACK LOOP
--
-- DASHI synthesis. This owner closes the scheduler loop after retrieval and
-- proof assessment. Search results may close, narrow, reopen, contradict or
-- leave a frontier underidentified. Every nonterminal change triggers a fresh
-- graph/fibre/cut computation; append-only provenance is retained.
------------------------------------------------------------------------

data FeedbackDisposition : Set where
  stopCandidate
  recomputeFrontier
  reopenForDefeater
  expandSearch
  continueSearch
  : FeedbackDisposition

feedbackDisposition :
  Assessment.ProofPaymentAssessment →
  Assessment.FrontierChange →
  FeedbackDisposition
feedbackDisposition Assessment.proofPaymentAdmitted Assessment.frontierClosed = stopCandidate
feedbackDisposition Assessment.proofPaymentAdmitted Assessment.frontierNarrowed = recomputeFrontier
feedbackDisposition Assessment.proofPaymentAdmitted Assessment.frontierReopened = recomputeFrontier
feedbackDisposition Assessment.proofPaymentAdmitted Assessment.frontierContradicted = reopenForDefeater
feedbackDisposition Assessment.proofPaymentAdmitted Assessment.frontierUnderidentified = expandSearch
feedbackDisposition Assessment.proofPaymentAdmitted Assessment.frontierUnchanged = continueSearch
feedbackDisposition Assessment.proofPaymentRejected Assessment.frontierContradicted = reopenForDefeater
feedbackDisposition Assessment.proofPaymentRejected change = continueSearch
feedbackDisposition Assessment.proofPaymentContested Assessment.frontierClosed = recomputeFrontier
feedbackDisposition Assessment.proofPaymentContested Assessment.frontierContradicted = reopenForDefeater
feedbackDisposition Assessment.proofPaymentContested Assessment.frontierUnderidentified = expandSearch
feedbackDisposition Assessment.proofPaymentContested change = recomputeFrontier
feedbackDisposition Assessment.proofPaymentCandidate Assessment.frontierUnderidentified = expandSearch
feedbackDisposition Assessment.proofPaymentCandidate change = recomputeFrontier
feedbackDisposition Assessment.proofPaymentUnresolved Assessment.frontierUnderidentified = expandSearch
feedbackDisposition Assessment.proofPaymentUnresolved change = continueSearch

------------------------------------------------------------------------
-- Exact transition calibrations.
------------------------------------------------------------------------

admittedClosureMayStop :
  feedbackDisposition Assessment.proofPaymentAdmitted Assessment.frontierClosed
  ≡ stopCandidate
admittedClosureMayStop = refl

admittedNarrowingRecomputes :
  feedbackDisposition Assessment.proofPaymentAdmitted Assessment.frontierNarrowed
  ≡ recomputeFrontier
admittedNarrowingRecomputes = refl

contradictionReopens :
  feedbackDisposition Assessment.proofPaymentRejected Assessment.frontierContradicted
  ≡ reopenForDefeater
contradictionReopens = refl

underidentificationExpands :
  feedbackDisposition Assessment.proofPaymentUnresolved Assessment.frontierUnderidentified
  ≡ expandSearch
underidentificationExpands = refl

unchangedUnresolvedContinues :
  feedbackDisposition Assessment.proofPaymentUnresolved Assessment.frontierUnchanged
  ≡ continueSearch
unchangedUnresolvedContinues = refl

------------------------------------------------------------------------
-- Reopening is typed by the residual that motivated the certified search.
-- These are scheduler routes only; they do not assert that the missing legal
-- proposition is true or that any retrieved source is authoritative.
------------------------------------------------------------------------

corePolicyReopenRequest : Refinement.LegalSelectiveReopenRequest
corePolicyReopenRequest = Refinement.requestForResidual
  (Residual.dutyResidualKind Climate.coreGovernmentPolicy)
  "duty:core-government-policy"

corePolicyReopensIssueProjection :
  Refinement.LegalSelectiveReopenRequest.reopenIssueProjection corePolicyReopenRequest
  ≡ true
corePolicyReopensIssueProjection = refl

statutoryCoherenceReopenRequest : Refinement.LegalSelectiveReopenRequest
statutoryCoherenceReopenRequest = Refinement.requestForResidual
  (Residual.dutyResidualKind Climate.statutoryCoherence)
  "duty:statutory-coherence"

statutoryCoherenceRoutesBackToStatute :
  Refinement.LegalSelectiveReopenRequest.acquisition statutoryCoherenceReopenRequest
  ≡ Residual.inspectStatutoryText
statutoryCoherenceRoutesBackToStatute = refl

herzogAuthorityMeaningReopenRequest : Refinement.LegalSelectiveReopenRequest
herzogAuthorityMeaningReopenRequest = Refinement.requestForResidual
  Residual.missingRelationalFeature
  "herzog:authority-meaning-before-after"

herzogPowerPrerequisiteReopenRequest : Refinement.LegalSelectiveReopenRequest
herzogPowerPrerequisiteReopenRequest = Refinement.requestForResidual
  Residual.missingInstitutionalConstraint
  "herzog:operational-power-prerequisite"

herzogIncidentWeldReopenRequest : Refinement.LegalSelectiveReopenRequest
herzogIncidentWeldReopenRequest = Refinement.requestForResidual
  Residual.missingFactualFeature
  "herzog:same-object-classification-order-unit-tactic-incident"

------------------------------------------------------------------------
-- The feedback contract explicitly preserves non-monotonic law.
------------------------------------------------------------------------

record AdaptiveLegalResearchFeedbackBoundary : Set where
  constructor adaptive-legal-research-feedback-boundary
  field
    assessedResultCanCloseOrDefeat : Bool
    assessedResultCanCloseOrDefeatIsTrue : assessedResultCanCloseOrDefeat ≡ true
    nonterminalResultRecomputesLiveFrontier : Bool
    nonterminalResultRecomputesLiveFrontierIsTrue :
      nonterminalResultRecomputesLiveFrontier ≡ true
    oldSourceHistoryPreserved : Bool
    oldSourceHistoryPreservedIsTrue : oldSourceHistoryPreserved ≡ true
    oldConclusionsFrozenAfterRefinement : Bool
    oldConclusionsFrozenAfterRefinementIsFalse :
      oldConclusionsFrozenAfterRefinement ≡ false
    minimalCutsMustBeRecomputed : Bool
    minimalCutsMustBeRecomputedIsTrue : minimalCutsMustBeRecomputed ≡ true
    frontierClosureCreatesActionAuthority : Bool
    frontierClosureCreatesActionAuthorityIsFalse :
      frontierClosureCreatesActionAuthority ≡ false

open AdaptiveLegalResearchFeedbackBoundary public

canonicalAdaptiveLegalResearchFeedbackBoundary : AdaptiveLegalResearchFeedbackBoundary
canonicalAdaptiveLegalResearchFeedbackBoundary =
  adaptive-legal-research-feedback-boundary
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data AssessedSearchResultCanOnlyOpenPaths : Set where
data FrontierClosedAutomaticallyAuthorisesAction : Set where
data RerunMayDiscardOldProvenance : Set where
data OldCutRemainsMinimalAfterSearch : Set where
data SearchFailureDeletesRequirement : Set where

assessmentMayActivateDefeater : AssessedSearchResultCanOnlyOpenPaths → ⊥
assessmentMayActivateDefeater ()

frontierClosureStillNeedsAuthority : FrontierClosedAutomaticallyAuthorisesAction → ⊥
frontierClosureStillNeedsAuthority ()

rerunPreservesHistory : RerunMayDiscardOldProvenance → ⊥
rerunPreservesHistory ()

cutMustBeRecomputed : OldCutRemainsMinimalAfterSearch → ⊥
cutMustBeRecomputed ()

searchFailureDoesNotDeleteRequirement : SearchFailureDeletesRequirement → ⊥
searchFailureDoesNotDeleteRequirement ()
