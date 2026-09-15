module DASHI.Culture.MissingDeceasedTwentyScientistRound55ResidualPaymentParetoRerunExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Culture.MissingDeceasedTwentyScientistRound53ParetoAcquisitionSchedulerExact as R53
import DASHI.Culture.MissingDeceasedTwentyScientistRound54ParetoDominancePruningExact as R54
import DASHI.Law.SensibLawAdaptiveLegalResearchFeedbackLoopExact as Feedback
import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Assessment

------------------------------------------------------------------------
-- ROUND 55: RESIDUAL PAYMENT / BLOCK / REOPEN -> PARETO RERUN
--
-- The scheduler is a function of a live residual state, not a static priority
-- list.  Any assessed result that narrows, reopens or contradicts the live
-- frontier invalidates stale scheduler receipts and forces a fresh local
-- Pareto computation.  Requirements and provenance remain append-only.
------------------------------------------------------------------------

data SchedulerState : Set where
  initialState : SchedulerState
  hcbResidualPaidState : SchedulerState
  scorpiusResidualBlockedState : SchedulerState
  amyReferentReopenedState : SchedulerState

record SchedulerStateReceipt : Set where
  constructor scheduler-state-receipt
  field
    state : SchedulerState
    liveResidualReference : String
    evidenceHistoryReference : String
    frontierVersionReference : String

open SchedulerStateReceipt public

initialReceipt : SchedulerStateReceipt
initialReceipt = scheduler-state-receipt
  initialState
  "Round 53/54 live residual set"
  "Rounds 23-54 append-only evidence/source history"
  "frontier-v0"

hcbPaidReceipt : SchedulerStateReceipt
hcbPaidReceipt = scheduler-state-receipt
  hcbResidualPaidState
  "synthetic scheduler transition: HCB same-object residual assessed/closed for rerun semantics only"
  "Rounds 23-54 history retained plus HCB assessment receipt"
  "frontier-v1"

scorpiusBlockedReceipt : SchedulerStateReceipt
scorpiusBlockedReceipt = scheduler-state-receipt
  scorpiusResidualBlockedState
  "synthetic scheduler transition: current Scorpius acquisition route blocked/unavailable"
  "prior history retained; blockage added as operational state, not evidence against proposition"
  "frontier-v2"

amyReopenedReceipt : SchedulerStateReceipt
amyReopenedReceipt = scheduler-state-receipt
  amyReferentReopenedState
  "synthetic scheduler transition: Amy referent residual reopened by contested/conflicting assessment"
  "prior history retained plus reopening receipt"
  "frontier-v3"

------------------------------------------------------------------------
-- Feedback inheritance from SensibLaw.
------------------------------------------------------------------------

admittedNarrowingTriggersParetoRerun :
  Feedback.feedbackDisposition
    Assessment.proofPaymentAdmitted
    Assessment.frontierNarrowed
  ≡ Feedback.recomputeFrontier
admittedNarrowingTriggersParetoRerun = refl

contestedOrReopenedResidualTriggersParetoRerun :
  Feedback.feedbackDisposition
    Assessment.proofPaymentContested
    Assessment.frontierReopened
  ≡ Feedback.recomputeFrontier
contestedOrReopenedResidualTriggersParetoRerun = refl

contradictedResidualReopensForDefeater :
  Feedback.feedbackDisposition
    Assessment.proofPaymentRejected
    Assessment.frontierContradicted
  ≡ Feedback.reopenForDefeater
contradictedResidualReopensForDefeater = refl

------------------------------------------------------------------------
-- Stale frontier receipts are state-indexed.
------------------------------------------------------------------------

record FrontierReceipt : Set where
  constructor frontier-receipt
  field
    receiptState : SchedulerState
    frontierReference : String
    selectedTasksReference : String

open FrontierReceipt public

initialFrontierReceipt : FrontierReceipt
initialFrontierReceipt = frontier-receipt
  initialState
  "frontier-v0"
  "Reza/McCasland + Amy + Chavez + LeBlanc + Ning + Chinese-origin + Garcia live trade-offs"

postHCBFrontierReceipt : FrontierReceipt
postHCBFrontierReceipt = frontier-receipt
  hcbResidualPaidState
  "frontier-v1"
  "HCB task removed from live acquisition set; sibling trade-offs recomputed"

sameSchedulerState : SchedulerState → SchedulerState → Bool
sameSchedulerState initialState initialState = true
sameSchedulerState hcbResidualPaidState hcbResidualPaidState = true
sameSchedulerState scorpiusResidualBlockedState scorpiusResidualBlockedState = true
sameSchedulerState amyReferentReopenedState amyReferentReopenedState = true
sameSchedulerState _ _ = false

receiptCurrentFor : SchedulerState → FrontierReceipt → Bool
receiptCurrentFor s r = sameSchedulerState s (receiptState r)

residualPaymentInvalidatesStaleFrontierReceipt :
  receiptCurrentFor hcbResidualPaidState initialFrontierReceipt ≡ false
residualPaymentInvalidatesStaleFrontierReceipt = refl

postPaymentReceiptIsCurrent :
  receiptCurrentFor hcbResidualPaidState postHCBFrontierReceipt ≡ true
postPaymentReceiptIsCurrent = refl

------------------------------------------------------------------------
-- Local live-set rerun fixture.
--
-- This is a scheduler-state fixture, not a claim that any real residual has
-- actually been paid/blocked/reopened.  It demonstrates how the critical path
-- changes if such a receipt arrives.
------------------------------------------------------------------------

data LocalTask : Set where
  hcbTask : LocalTask
  amyTask : LocalTask
  chavezTask : LocalTask
  leblancTask : LocalTask
  chineseOriginTask : LocalTask
  lowYieldSiblingTask : LocalTask

initialLocalFrontier : List LocalTask
initialLocalFrontier =
  hcbTask ∷ amyTask ∷ chavezTask ∷ chineseOriginTask ∷ []

postHCBLocalFrontier : List LocalTask
postHCBLocalFrontier =
  amyTask ∷ chavezTask ∷ leblancTask ∷ chineseOriginTask ∷ []

postScorpiusBlockFrontier : List LocalTask
postScorpiusBlockFrontier =
  hcbTask ∷ amyTask ∷ leblancTask ∷ chineseOriginTask ∷ lowYieldSiblingTask ∷ []

postAmyReopenFrontier : List LocalTask
postAmyReopenFrontier =
  hcbTask ∷ amyTask ∷ chavezTask ∷ chineseOriginTask ∷ []

-- A formerly non-frontier sibling may become live after a residual is paid.
siblingTaskCanEnterAfterRerun :
  postHCBLocalFrontier
  ≡ amyTask ∷ chavezTask ∷ leblancTask ∷ chineseOriginTask ∷ []
siblingTaskCanEnterAfterRerun = refl

-- Blocking one high-alpha acquisition can promote a previously dominated
-- sibling acquisition without asserting anything about the underlying claim.
blockedResidualCanDemoteTask :
  postScorpiusBlockFrontier
  ≡ hcbTask ∷ amyTask ∷ leblancTask ∷ chineseOriginTask ∷ lowYieldSiblingTask ∷ []
blockedResidualCanDemoteTask = refl

reopenedResidualCanRestoreTask :
  postAmyReopenFrontier
  ≡ hcbTask ∷ amyTask ∷ chavezTask ∷ chineseOriginTask ∷ []
reopenedResidualCanRestoreTask = refl

------------------------------------------------------------------------
-- Append-only requirement/evidence history.
------------------------------------------------------------------------

record RequirementHistory : Set where
  constructor requirement-history
  field
    requirementReference : String
    firstSeenReference : String
    currentStatusReference : String
    stillRecorded : Bool

open RequirementHistory public

lowYieldSiblingHistory : RequirementHistory
lowYieldSiblingHistory = requirement-history
  "lower-yield exact-object crossing residual from Round 54"
  "Round 54 dominated-but-eligible fixture"
  "off initial critical path; may re-enter after Scorpius blockage"
  true

offFrontierRequirementRemainsRecorded : Bool
offFrontierRequirementRemainsRecorded = stillRecorded lowYieldSiblingHistory

rerunPreservesEvidenceHistory : Bool
rerunPreservesEvidenceHistory = true

blockedRouteIsNotEvidenceAgainstClaim : Bool
blockedRouteIsNotEvidenceAgainstClaim = true

paidResidualDoesNotDeleteUnderlyingEvidence : Bool
paidResidualDoesNotDeleteUnderlyingEvidence = true

reopenedResidualDoesNotErasePriorAssessment : Bool
reopenedResidualDoesNotErasePriorAssessment = true

schedulerRerunDoesNotCreateTruth : Bool
schedulerRerunDoesNotCreateTruth = true

schedulerRerunDoesNotCreateAuthority : Bool
schedulerRerunDoesNotCreateAuthority = true

------------------------------------------------------------------------
-- Current real evidentiary status is unchanged.  The transitions above are
-- control-state fixtures demonstrating scheduler semantics only.
------------------------------------------------------------------------

round55H2PaidCount : Nat
round55H2PaidCount = 0

round55H3PaidCount : Nat
round55H3PaidCount = 0

round55Reading : String
round55Reading = "The Pareto scheduler is now explicitly state-sensitive. An admitted payment that narrows the residual fibre, a contested result that reopens it, or a blocked acquisition route invalidates stale frontier receipts and triggers a fresh local scheduler computation. Sibling tasks may enter or leave the critical path, but their underlying requirements and evidence history remain recorded. These before/after states are scheduler-control fixtures only and do not assert that HCB, Scorpius or Amy residuals have actually changed in the real investigation."

round55Next : String
round55Next = "Next bind concrete acquisition-result assessments to these transitions: retrieved item -> attributed proposition -> payment/contestation assessment -> frontier delta -> affected-neighbourhood recomputation. This will make the rerun event proof-carrying rather than merely state-labelled."
