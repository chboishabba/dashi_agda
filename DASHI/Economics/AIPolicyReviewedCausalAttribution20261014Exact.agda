module DASHI.Economics.AIPolicyReviewedCausalAttribution20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AIPolicyCausalEstimandIdentification20261012Exact as Policy
import DASHI.Law.SensibLawRealMatterReviewDecisionExact as Review

------------------------------------------------------------------------
-- REVIEWED POLICY-CAUSAL ATTRIBUTION GATE
--
-- Productive local reuse of master-available SensibLaw review machinery.
-- An identified causal bridge still requires exact human review binding before
-- it can be used as reviewed attribution evidence.  Review and identification
-- are independent obligations; neither manufactures the other or motive.
------------------------------------------------------------------------

GenericHumanReviewReceipt : Set
GenericHumanReviewReceipt = Review.GenericHumanReviewReceipt

ExactReviewItemBinding : Set
ExactReviewItemBinding = Review.ExactReviewItemBinding

record ReviewedIdentifiedPolicyCausalBridge : Set₂ where
  constructor reviewed-identified-policy-causal-bridge
  field
    identifiedBridge : Policy.IdentifiedPolicyCausalBridge
    humanReview : Review.GenericHumanReviewReceipt
    exactReviewBinding : Review.ExactReviewItemBinding
    reviewItemMatchesPolicyClaim :
      Review.reviewItemRef humanReview ≡ Policy.policyClaimReference identifiedBridge
    reviewAcceptedOrQualified :
      Review.acceptedOrQualified exactReviewBinding ≡ true
    reviewedCausalPremiseRef : String
    reviewReceiptIdentityRef : String
    establishesIntentionalCapture : Bool

open ReviewedIdentifiedPolicyCausalBridge public

record ReviewedPolicyAttributionStatus : Set where
  constructor reviewed-policy-attribution-status
  field
    policySubstratePaid : Bool
    realisedCostVectorPaid : Bool
    marketResponsePaid : Bool
    causalEstimandPaid : Bool
    identificationGatePaid : Bool
    exactHumanReviewPaid : Bool
    reviewedSameObjectBridgePaid : Bool
    intentionalCapturePaid : Bool

open ReviewedPolicyAttributionStatus public

currentAustralianReviewedPolicyStatus : ReviewedPolicyAttributionStatus
currentAustralianReviewedPolicyStatus = reviewed-policy-attribution-status
  true false false false false false false false

exactHumanReviewStillOpen :
  exactHumanReviewPaid currentAustralianReviewedPolicyStatus ≡ false
exactHumanReviewStillOpen = refl

reviewedSameObjectBridgeStillOpen :
  reviewedSameObjectBridgePaid currentAustralianReviewedPolicyStatus ≡ false
reviewedSameObjectBridgeStillOpen = refl

data ReviewCreatesIdentificationPermission : Set where
data IdentificationCreatesReviewPermission : Set where
data ReviewedBridgeCreatesIntentionalCapturePermission : Set where
data ReviewMetadataCreatesMeasuredBurdenPermission : Set where

reviewDoesNotCreateIdentification : ReviewCreatesIdentificationPermission → ⊥
reviewDoesNotCreateIdentification ()

identificationDoesNotCreateReview : IdentificationCreatesReviewPermission → ⊥
identificationDoesNotCreateReview ()

reviewedCausalBridgeDoesNotCreateIntentionalCapture :
  ReviewedBridgeCreatesIntentionalCapturePermission → ⊥
reviewedCausalBridgeDoesNotCreateIntentionalCapture ()

reviewMetadataDoesNotCreateMeasuredBurden :
  ReviewMetadataCreatesMeasuredBurdenPermission → ⊥
reviewMetadataDoesNotCreateMeasuredBurden ()

boundary : String
boundary =
  "AI-policy causal attribution now has an explicit final review gate using the master-available SensibLaw GenericHumanReviewReceipt and ExactReviewItemBinding. A policy causal claim must first pay the typed estimand, identification-family gate, realised same-basis cost and market-response obligations, and then bind an accepted/qualified human review to the exact policy claim. Review does not create identification or measured burden; identification does not create review; even a reviewed identified bridge does not by itself establish intentional regulatory capture."
