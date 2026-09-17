module DASHI.Wikimedia.MaboReviewedEvidencePaymentExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.LeanSlrWorldObservationBidiExact as GoldenObservation
import DASHI.Wikimedia.MaboWorldObservationInteropExact as Observation

------------------------------------------------------------------------
-- Explicit review boundary between a retrieved observation and residual payment.
--
-- A Wikidata/OALC/article observation never chooses its own evidence role. The
-- consumer requirement and reviewer explicitly identify the evidence coordinate;
-- only that reviewed coordinate may emit payment for the exact gap/obligation.
------------------------------------------------------------------------

data EvidenceCoordinate : Set where
  sourceIdentity : EvidenceCoordinate
  sameObject : EvidenceCoordinate
  authority : EvidenceCoordinate
  mechanism : EvidenceCoordinate
  quantification : EvidenceCoordinate
  probability : EvidenceCoordinate
  counterfactual : EvidenceCoordinate
  instrumentComparison : EvidenceCoordinate
  incidence : EvidenceCoordinate
  classification : EvidenceCoordinate

record ReviewedEvidenceCoordinate : Set where
  constructor reviewed-evidence-coordinate
  field
    reviewReference : String
    consumerReference : String
    requirementReference : String
    coordinate : EvidenceCoordinate
    sourceRevisionReference : String
    evidenceObservationReference : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open ReviewedEvidenceCoordinate public

maboParticipantIdentityReview : ReviewedEvidenceCoordinate
maboParticipantIdentityReview =
  reviewed-evidence-coordinate
    "review:mabo:P710:Q975866"
    "consumer:mabo-100-identity-classes"
    "participant-identity"
    sameObject
    (GoldenObservation.sourceRevisionReference Observation.maboP710Observation)
    "query:mabo:P710:Q975866"
    true refl false refl false refl false refl

record ReviewedEvidencePaymentReceipt : Set where
  constructor reviewed-evidence-payment-receipt
  field
    reviewEmitted : Bool
    gapPaymentEmitted : Bool
    obligationPaymentEmitted : Bool
    requirementsPaid : Nat
    requirementsUnpaid : Nat
    paymentCreatesSemanticAuthority : Bool
    paymentPromotesApplicability : Bool
    paymentPromotesClaimTruth : Bool

open ReviewedEvidencePaymentReceipt public

maboParticipantIdentityPayment : ReviewedEvidencePaymentReceipt
maboParticipantIdentityPayment =
  reviewed-evidence-payment-receipt
    true
    true
    true
    1
    0
    false
    false
    false

maboParticipantIdentityPaid : requirementsPaid maboParticipantIdentityPayment ≡ 1
maboParticipantIdentityPaid = refl

maboParticipantIdentityNoLongerUnpaid : requirementsUnpaid maboParticipantIdentityPayment ≡ 0
maboParticipantIdentityNoLongerUnpaid = refl

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

data ObservationInfersEvidenceCoordinate : Set where
data WikidataPropertyEqualsSameObjectReview : Set where
data AuthoritySourceCandidateEqualsLegalAuthority : Set where
data RetrievedObservationEqualsResidualPayment : Set where
data ReviewedPaymentEqualsClaimTruth : Set where

observationDoesNotInferEvidenceCoordinate : ObservationInfersEvidenceCoordinate → ⊥
observationDoesNotInferEvidenceCoordinate ()

wikidataPropertyDoesNotEqualSameObjectReview : WikidataPropertyEqualsSameObjectReview → ⊥
wikidataPropertyDoesNotEqualSameObjectReview ()

authoritySourceCandidateDoesNotEqualLegalAuthority : AuthoritySourceCandidateEqualsLegalAuthority → ⊥
authoritySourceCandidateDoesNotEqualLegalAuthority ()

retrievedObservationDoesNotEqualResidualPayment : RetrievedObservationEqualsResidualPayment → ⊥
retrievedObservationDoesNotEqualResidualPayment ()

reviewedPaymentDoesNotEqualClaimTruth : ReviewedPaymentEqualsClaimTruth → ⊥
reviewedPaymentDoesNotEqualClaimTruth ()
