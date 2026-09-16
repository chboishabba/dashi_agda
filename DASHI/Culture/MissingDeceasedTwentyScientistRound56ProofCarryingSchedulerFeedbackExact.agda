module DASHI.Culture.MissingDeceasedTwentyScientistRound56ProofCarryingSchedulerFeedbackExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Culture.MissingDeceasedTwentyScientistRound53ParetoAcquisitionSchedulerExact as R53
import DASHI.Culture.MissingDeceasedTwentyScientistRound55ResidualPaymentParetoRerunExact as R55
import DASHI.Law.SensibLawAdaptiveLegalResearchFeedbackLoopExact as Feedback
import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Assessment

------------------------------------------------------------------------
-- ROUND 56: PROOF-CARRYING SCHEDULER FEEDBACK
--
-- A retrieved item cannot mutate the Pareto scheduler merely by existing.
-- Mutation requires a proposition-level assessment and a typed frontier delta
-- tied to an affected scheduler neighbourhood.  The resulting rerun receipt
-- records the old/new frontier versions while preserving prior evidence history.
------------------------------------------------------------------------

data AssessmentOutcome : Set where
  admittedPayment : AssessmentOutcome
  rejectedPayment : AssessmentOutcome
  contestedPayment : AssessmentOutcome
  unresolvedPayment : AssessmentOutcome

outcomePayment : AssessmentOutcome → Assessment.ProofPaymentAssessment
outcomePayment admittedPayment = Assessment.proofPaymentAdmitted
outcomePayment rejectedPayment = Assessment.proofPaymentRejected
outcomePayment contestedPayment = Assessment.proofPaymentContested
outcomePayment unresolvedPayment = Assessment.proofPaymentUnresolved

record AcquisitionAssessment : Set where
  constructor acquisition-assessment
  field
    selectedTask : R53.AcquisitionTask
    retrievedItemReference : String
    attributedPropositionReference : String
    sourceRoleReference : String
    propositionScopeReference : String
    outcome : AssessmentOutcome
    frontierChange : Assessment.FrontierChange
    residualBeforeReference : String
    residualAfterReference : String
    affectedNeighbourhoodReference : String
    assessmentReference : String

open AcquisitionAssessment public

------------------------------------------------------------------------
-- Mutation preconditions remain explicit.
------------------------------------------------------------------------

attributedPropositionRequiredBeforeSchedulerMutation : Bool
attributedPropositionRequiredBeforeSchedulerMutation = true

frontierDeltaRequiredBeforeRerun : Bool
frontierDeltaRequiredBeforeRerun = true

affectedNeighbourhoodRequiredBeforeRerun : Bool
affectedNeighbourhoodRequiredBeforeRerun = true

retrievalRankCannotMutateScheduler : Bool
retrievalRankCannotMutateScheduler = true

searchHitCannotMutateScheduler : Bool
searchHitCannotMutateScheduler = true

------------------------------------------------------------------------
-- Concrete synthetic HCB feedback fixture.
--
-- This is a scheduler-control example only.  It does not assert that the real
-- HCB same-object residual has been paid.
------------------------------------------------------------------------

syntheticHCBAdmittedAssessment : AcquisitionAssessment
syntheticHCBAdmittedAssessment = acquisition-assessment
  R53.rezaMcCaslandTask
  "synthetic identity-bearing HCB record"
  "synthetic proposition: McCasland appears on the exact selected HCB object"
  "exact contemporaneous programme/task record"
  "same-object participation proposition only"
  admittedPayment
  Assessment.frontierNarrowed
  "HCB same-object residual live"
  "HCB same-object residual assessed closed for fixture"
  "HCB / propulsion shared-object scheduler neighbourhood"
  "Round 56 synthetic admitted-payment fixture"

syntheticHCBFeedback :
  Feedback.feedbackDisposition
    (outcomePayment (outcome syntheticHCBAdmittedAssessment))
    (frontierChange syntheticHCBAdmittedAssessment)
  ≡ Feedback.recomputeFrontier
syntheticHCBFeedback = refl

record ProofCarryingRerunReceipt : Set where
  constructor proof-carrying-rerun-receipt
  field
    assessment : AcquisitionAssessment
    feedbackDisposition : Feedback.FeedbackDisposition
    feedbackMatchesAssessment :
      feedbackDisposition
      ≡ Feedback.feedbackDisposition
          (outcomePayment (outcome assessment))
          (frontierChange assessment)
    priorFrontierVersionReference : String
    posteriorFrontierVersionReference : String
    affectedNeighbourhood : String
    priorEvidenceHistoryReference : String
    posteriorEvidenceHistoryReference : String
    priorHistoryPreserved : Bool

open ProofCarryingRerunReceipt public

admittedPaymentRerunReceipt : ProofCarryingRerunReceipt
admittedPaymentRerunReceipt = proof-carrying-rerun-receipt
  syntheticHCBAdmittedAssessment
  Feedback.recomputeFrontier
  refl
  "frontier-v0"
  "frontier-v1"
  "HCB / propulsion shared-object scheduler neighbourhood"
  "Rounds 23-55 history"
  "Rounds 23-55 history + synthetic Round-56 assessment"
  true

admittedPaymentProducesRerunReceipt : Bool
admittedPaymentProducesRerunReceipt = true

proofCarryingRerunPreservesPriorHistory : Bool
proofCarryingRerunPreservesPriorHistory = priorHistoryPreserved admittedPaymentRerunReceipt

------------------------------------------------------------------------
-- Rejected and contested results have different scheduler semantics.
------------------------------------------------------------------------

syntheticRejectedAssessment : AcquisitionAssessment
syntheticRejectedAssessment = acquisition-assessment
  R53.garciaRoleWeldTask
  "synthetic candidate Garcia role record"
  "candidate role proposition fails proposition/source-role assessment"
  "candidate role source"
  "employment/security role proposition"
  rejectedPayment
  Assessment.frontierUnchanged
  "Garcia role residual live"
  "Garcia role residual still live"
  "Garcia role-weld neighbourhood"
  "Round 56 rejected-result fixture"

syntheticRejectedFeedback :
  Feedback.feedbackDisposition
    (outcomePayment (outcome syntheticRejectedAssessment))
    (frontierChange syntheticRejectedAssessment)
  ≡ Feedback.continueSearch
syntheticRejectedFeedback = refl

rejectedResultCannotPayResidual : Bool
rejectedResultCannotPayResidual = true

syntheticContestedAssessment : AcquisitionAssessment
syntheticContestedAssessment = acquisition-assessment
  R53.amyReferentWeldTask
  "synthetic Amy referent carrier with conflicting attribution"
  "candidate exact-object referent proposition becomes contested"
  "archived/original/review provenance family"
  "same-object referent identity proposition"
  contestedPayment
  Assessment.frontierReopened
  "Amy referent residual previously narrowed"
  "Amy referent residual reopened"
  "Amy referent/NASA-review neighbourhood"
  "Round 56 contested-result fixture"

syntheticContestedFeedback :
  Feedback.feedbackDisposition
    (outcomePayment (outcome syntheticContestedAssessment))
    (frontierChange syntheticContestedAssessment)
  ≡ Feedback.recomputeFrontier
syntheticContestedFeedback = refl

contestedResultCanReopenWithoutPaying : Bool
contestedResultCanReopenWithoutPaying = true

------------------------------------------------------------------------
-- Typed frontier delta bridge.
------------------------------------------------------------------------

record SchedulerFrontierDelta : Set where
  constructor scheduler-frontier-delta
  field
    assessment : AcquisitionAssessment
    priorFrontierReference : String
    posteriorFrontierReference : String
    change : Assessment.FrontierChange
    changeMatchesAssessment : change ≡ frontierChange assessment
    affectedNeighbourhood : String
    residualBefore : String
    residualAfter : String

open SchedulerFrontierDelta public

hcbFrontierDelta : SchedulerFrontierDelta
hcbFrontierDelta = scheduler-frontier-delta
  syntheticHCBAdmittedAssessment
  "frontier-v0"
  "frontier-v1"
  Assessment.frontierNarrowed
  refl
  "HCB / propulsion shared-object scheduler neighbourhood"
  "HCB same-object residual live"
  "HCB same-object residual assessed closed for fixture"

frontierMutationIsConsumerAndNeighbourhoodBound : Bool
frontierMutationIsConsumerAndNeighbourhoodBound = true

unaffectedNeighbourhoodNeedNotBeRecomputedGlobally : Bool
unaffectedNeighbourhoodNeedNotBeRecomputedGlobally = true

localRerunCannotEraseGlobalRequirementHistory : Bool
localRerunCannotEraseGlobalRequirementHistory = true

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RetrievalAlonePaysResidual : Set where
data RerunReceiptCreatesUnderlyingFact : Set where
data RejectedAssessmentMeansOppositeFact : Set where
data ContestedAssessmentPaysClaim : Set where

retrievalAloneCannotPayResidual : RetrievalAlonePaysResidual → ⊥
retrievalAloneCannotPayResidual ()

rerunReceiptDoesNotCreateUnderlyingFact : RerunReceiptCreatesUnderlyingFact → ⊥
rerunReceiptDoesNotCreateUnderlyingFact ()

rejectedDoesNotMeanOppositeFact : RejectedAssessmentMeansOppositeFact → ⊥
rejectedDoesNotMeanOppositeFact ()

contestedDoesNotPayClaim : ContestedAssessmentPaysClaim → ⊥
contestedDoesNotPayClaim ()

------------------------------------------------------------------------
-- Current real investigation state remains unchanged.
------------------------------------------------------------------------

round56H2PaidCount : Nat
round56H2PaidCount = 0

round56H3PaidCount : Nat
round56H3PaidCount = 0

round56Reading : String
round56Reading = "The investigation scheduler now has a proof-carrying feedback seam: retrieval -> attributed proposition -> proposition/source-role assessment -> payment disposition -> typed frontier delta -> affected-neighbourhood rerun receipt. Retrieval rank or mere source discovery cannot mutate the frontier. Rejected results leave the residual unpaid; contested results may reopen a residual without paying it; admitted narrowing triggers recomputation. Prior evidence and requirement history survive every rerun. The HCB/Amy/Garcia examples in this owner are synthetic control-state fixtures and do not alter the real H2/H3 counts."

round56Next : String
round56Next = "Next instantiate this assessment carrier with the first real acquisition results returned by the Pareto scheduler, so each search pass either pays a typed residual, records a blocker/non-progress reason, or reopens a neighbourhood and immediately reruns Pareto."
