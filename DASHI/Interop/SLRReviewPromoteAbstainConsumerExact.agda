module DASHI.Interop.SLRReviewPromoteAbstainConsumerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRWorldModelSuiteConvergenceRoadmapExact as World
import DASHI.Interop.SLRC029WorldConstraintFibreBridgeExact as C029World
import DASHI.Policy.ABC730C029LegalMachineryHyperfabricExact as C029

------------------------------------------------------------------------
-- REVIEW / PROMOTE / ABSTAIN CONSUMER
--
-- Runtime companion:
--   tools/slr-discourse-reconstruct/slr_review_disposition.py
--   schema = slr-review-disposition-v1
--
-- This consumer never promotes semantic truth.  It only decides whether a
-- candidate should be rejected by a hard consumer veto, retained/abstained for
-- open residuals, or passed to a separate promotion-review surface once both
-- compatibility and consumer adequacy are supplied.
------------------------------------------------------------------------

data ReviewDisposition : Set where
  retainCandidate : ReviewDisposition
  abstainForResidual : ReviewDisposition
  rejectByConsumerVeto : ReviewDisposition
  eligibleForSeparatePromotionReview : ReviewDisposition

record ReviewInput : Set where
  constructor reviewInput
  field
    candidateReference : String
    worldCompatible : Bool
    consumerAdequate : Bool
    residualOpen : Bool
    alreadyTruthPromoted : Bool
    consumerReference : String
    residualReference : String

open ReviewInput public

review : ReviewInput → ReviewDisposition
review input with worldCompatible input
... | false = rejectByConsumerVeto
... | true with consumerAdequate input
...   | false = abstainForResidual
...   | true with residualOpen input
...     | true = abstainForResidual
...     | false = eligibleForSeparatePromotionReview

------------------------------------------------------------------------
-- Current C029 consumer state.
------------------------------------------------------------------------

canonicalC029ReviewInput : ReviewInput
canonicalC029ReviewInput = reviewInput
  "sl.candidate_world_model.v0_1:C029"
  true
  false
  true
  false
  "ABC730 C029 unintended-consequences comparative/evaluative consumer"
  "settlementClassifierResidual"

canonicalC029Disposition :
  review canonicalC029ReviewInput ≡ abstainForResidual
canonicalC029Disposition = refl

currentC029ResidualStillSettlementClassifier :
  C029.firstC029Residual C029.canonicalC029Cutset ≡ C029.settlementClassifierResidual
currentC029ResidualStillSettlementClassifier = C029.currentFirstResidualIsSettlementClassifier

worldBridgeAlsoAbstains :
  C029World.reviewC029Candidate C029World.canonicalC029WorldConstraintState ≡
  C029World.abstainForResidual
worldBridgeAlsoAbstains = C029World.currentReviewDisposition

------------------------------------------------------------------------
-- Separate promotion receipt surface.
--
-- Eligibility is intentionally weaker than promotion.  A later authority may
-- issue a promotion receipt; this consumer cannot manufacture one.
------------------------------------------------------------------------

record PromotionReviewReceipt : Set where
  constructor promotionReviewReceipt
  field
    candidateReference : String
    reviewerReference : String
    evidenceBundleReference : String
    consumerAdequacyReference : String
    authorityReference : String
    promotionApproved : Bool
    receiptReference : String

open PromotionReviewReceipt public

data ReviewEligibilityCreatesPromotionReceipt : Set where

eligibilityCannotManufacturePromotion :
  ReviewEligibilityCreatesPromotionReceipt → ⊥
eligibilityCannotManufacturePromotion ()

------------------------------------------------------------------------
-- Runtime contract.
------------------------------------------------------------------------

record RuntimeReviewContract : Set where
  constructor runtimeReviewContract
  field
    schemaReference : String
    requiresCandidateWorldModel : Bool
    requiresWorldConstraintFibre : Bool
    consumerGateMayBeUnsupplied : Bool
    incompatibleCandidateRejected : Bool
    inadequateCandidateAbstained : Bool
    residualCandidateAbstained : Bool
    eligibleCandidatePromotedAutomatically : Bool
    promotionPerformedByRuntime : Bool
    candidateOnly : Bool

open RuntimeReviewContract public

canonicalRuntimeReviewContract : RuntimeReviewContract
canonicalRuntimeReviewContract = runtimeReviewContract
  "slr-review-disposition-v1"
  true
  true
  true
  true
  true
  true
  false
  false
  true

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data AbstentionMeansClaimFalse : Set where
data RejectionMeansWorldPropositionFalse : Set where
data EligibilityMeansTruth : Set where
data UnpaidConsumerMayBeReplacedByConfidenceScore : Set where
data OpenResidualMayBeDroppedForConvenience : Set where

abstentionDoesNotMeanFalse : AbstentionMeansClaimFalse → ⊥
abstentionDoesNotMeanFalse ()

rejectionDoesNotMeanWorldFalse : RejectionMeansWorldPropositionFalse → ⊥
rejectionDoesNotMeanWorldFalse ()

eligibilityDoesNotMeanTruth : EligibilityMeansTruth → ⊥
eligibilityDoesNotMeanTruth ()

consumerDebtIsNotConfidenceScore : UnpaidConsumerMayBeReplacedByConfidenceScore → ⊥
consumerDebtIsNotConfidenceScore ()

openResidualMayNotBeDropped : OpenResidualMayBeDroppedForConvenience → ⊥
openResidualMayNotBeDropped ()

------------------------------------------------------------------------
-- Existing-owner anchors.
------------------------------------------------------------------------

worldRoadmapAnchor : World.SuiteConvergenceLaw
worldRoadmapAnchor = World.canonicalSuiteConvergenceLaw

worldC029StateAnchor : C029World.C029WorldConstraintState
worldC029StateAnchor = C029World.canonicalC029WorldConstraintState

c029CutsetAnchor : C029.C029LegalEvidenceCutset
c029CutsetAnchor = C029.canonicalC029Cutset
