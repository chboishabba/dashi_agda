module DASHI.Interop.SLRReviewedEvidencePaymentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRBinaryWorldWireParityExact as WorldWire
import DASHI.Interop.SLRConsumerRequirementV2Exact as ConsumerV2
import DASHI.Interop.SLRAppendOnlyActiveResidualFrontierExact as Frontier

------------------------------------------------------------------------
-- REVIEWED SUBSTANTIVE EVIDENCE PAYMENT
--
-- Runtime owner:
--   chboishabba/slr :: crates/sl-evidence-payment
--
-- Review wire SLRE v1:
--   consumerId, requirementId, evidence-coordinate tag,
--   evidenceReference, reviewerReference, disposition.
--
-- Every review is append-only RVW1 (SLRW kind 9). Only paysObligation may
-- additionally emit PAY2 kind-8 receipts targeting the exact active GAP2 and
-- OBL2 residual ids. Partial/block/wrong-type reviews are retained but do not
-- contract the frontier.
------------------------------------------------------------------------

reviewWireVersion : Nat
reviewWireVersion = 1

data ReviewDisposition : Set where
  paysObligation : ReviewDisposition
  partialEvidenceOnly : ReviewDisposition
  measurementBlockOnly : ReviewDisposition
  rejectedWrongType : ReviewDisposition

reviewDispositionTag : ReviewDisposition → Nat
reviewDispositionTag paysObligation = 1
reviewDispositionTag partialEvidenceOnly = 2
reviewDispositionTag measurementBlockOnly = 3
reviewDispositionTag rejectedWrongType = 4

reviewWorldWireKindTag : Nat
reviewWorldWireKindTag = WorldWire.worldWireKindTag WorldWire.review

paymentWorldWireKindTag : Nat
paymentWorldWireKindTag = WorldWire.worldWireKindTag WorldWire.payment

record ReviewedEvidencePaymentParity : Set where
  constructor reviewedEvidencePaymentParity
  field
    reviewWireMagicIsSLRE : Bool
    reviewWireVersionIsOne : Bool
    evidenceCoordinateUsesConsumerV2Tags : Bool
    dispositionTagsOneThroughFourExact : Bool
    reviewUsesWorldWireKindNine : Bool
    paymentUsesWorldWireKindEight : Bool
    reviewMagicIsRVW1 : Bool
    substantivePaymentMagicIsPAY2 : Bool
    exactActiveOBL2Required : Bool
    coordinateMustMatchTargetObligation : Bool
    everyReviewIsRetained : Bool
    paysDispositionEmitsTwoPayments : Bool
    partialDispositionContractsFrontier : Bool
    measurementBlockContractsFrontier : Bool
    wrongTypeContractsFrontier : Bool
    paymentTargetsExactGapAndObligationIds : Bool
    evidenceReviewCreatesClaimTruth : Bool
    evidenceReviewCreatesSemanticAuthority : Bool
    postgresPerformsEvidenceReview : Bool
    jsonTransportUsed : Bool
    regexParserUsed : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open ReviewedEvidencePaymentParity public

canonicalReviewedEvidencePaymentParity : ReviewedEvidencePaymentParity
canonicalReviewedEvidencePaymentParity =
  reviewedEvidencePaymentParity
    true true true true true true true true true true true true
    false false false true false false false false false true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PartialEvidenceContractsFrontier : Set where
data WrongTypeEvidenceContractsFrontier : Set where
data EvidenceReviewCreatesClaimTruth : Set where
data EvidenceReviewCreatesSemanticAuthority : Set where
data PostgresPerformsEvidenceReview : Set where

partialEvidenceCannotContractFrontier : PartialEvidenceContractsFrontier → ⊥
partialEvidenceCannotContractFrontier ()

wrongTypeEvidenceCannotContractFrontier : WrongTypeEvidenceContractsFrontier → ⊥
wrongTypeEvidenceCannotContractFrontier ()

evidenceReviewDoesNotCreateClaimTruth : EvidenceReviewCreatesClaimTruth → ⊥
evidenceReviewDoesNotCreateClaimTruth ()

evidenceReviewDoesNotCreateSemanticAuthority : EvidenceReviewCreatesSemanticAuthority → ⊥
evidenceReviewDoesNotCreateSemanticAuthority ()

postgresDoesNotPerformEvidenceReview : PostgresPerformsEvidenceReview → ⊥
postgresDoesNotPerformEvidenceReview ()

activeFrontierAnchor : Frontier.ActiveResidualFrontierParity
activeFrontierAnchor = Frontier.canonicalActiveResidualFrontierParity

mechanismCoordinateTagAnchor : Nat
mechanismCoordinateTagAnchor = ConsumerV2.evidenceCoordinateTag ConsumerV2.mechanism
