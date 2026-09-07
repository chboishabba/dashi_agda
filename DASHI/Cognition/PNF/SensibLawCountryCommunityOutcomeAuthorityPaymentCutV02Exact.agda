module DASHI.Cognition.PNF.SensibLawCountryCommunityOutcomeAuthorityPaymentCutV02Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawCountryCommunityOutcomeCandidateV02Exact as Outcome
import DASHI.Cognition.PNF.SensibLawCountryCommunityAuthorityAdmissibilityV02Exact as Authority
import DASHI.Cognition.PNF.SensibLawCountryRealisedRepairProofSearchBridgeV02Exact as Bridge

------------------------------------------------------------------------
-- COMMUNITY OUTCOME + AUTHORITY PAYMENT CUT V02
--
-- The repository now owns the candidate/source and authority-admission
-- architecture.  The remaining mathematical/evidentiary seam is intentionally
-- narrow: pick one declared operational consumer and inhabit the exact
-- consumer/outcome correspondence plus current authority mandate.
------------------------------------------------------------------------

data PaymentCutState : Set where
  candidateAvailable
  admissionEvidenceMissing
  paymentAdmitted
  : PaymentCutState

currentOutcomeCandidateState : PaymentCutState
currentOutcomeCandidateState = candidateAvailable

currentAuthorityAdmissionState : PaymentCutState
currentAuthorityAdmissionState = admissionEvidenceMissing

record CommunityOutcomePaymentEvidence
       (candidate : Outcome.CommunityOutcomeCandidate) : Set₁ where
  constructor community-outcome-payment-evidence
  field
    declaredConsumerReference : String
    candidateActuallyDefinesSatisfactoryOutcomeForConsumer : Set
    propositionCorrespondsToDeclaredConsumer : Set
    sourceProvenancePreserved : Set
    communityOriginRetained : Set
    paymentReference : String

record PaidCommunityOutcomeV02
       (candidate : Outcome.CommunityOutcomeCandidate) : Set₁ where
  constructor paid-community-outcome-v02
  field
    evidence : CommunityOutcomePaymentEvidence candidate
    nextResidualReference : String

payCommunityOutcome :
  (candidate : Outcome.CommunityOutcomeCandidate) →
  CommunityOutcomePaymentEvidence candidate →
  PaidCommunityOutcomeV02 candidate
payCommunityOutcome candidate evidence = paid-community-outcome-v02
  evidence
  "communityAuthorityCapacityResidualV02"

record JointOutcomeAuthorityPaymentV02
       (outcomeCandidate : Outcome.CommunityOutcomeCandidate)
       (authorityCandidate : Authority.CommunityAuthorityReceiptV02) : Set₁ where
  constructor joint-outcome-authority-payment-v02
  field
    outcomePayment : PaidCommunityOutcomeV02 outcomeCandidate
    authorityAdmissionEvidence : Authority.AuthorityAdmissionEvidence authorityCandidate
    sameConsumerAcrossOutcomeAndAuthority : Set
    sameOutcomeAcrossPaymentAndAuthority : Set
    jointProvenancePreserved : Set
    currentMandateValid : Set
    jointPaymentReference : String

compileJointPayment :
  {outcomeCandidate : Outcome.CommunityOutcomeCandidate} →
  {authorityCandidate : Authority.CommunityAuthorityReceiptV02} →
  JointOutcomeAuthorityPaymentV02 outcomeCandidate authorityCandidate →
  Authority.AdmittedCommunityAuthorityV02 authorityCandidate
compileJointPayment payment =
  Authority.admitAuthority _
    (JointOutcomeAuthorityPaymentV02.authorityAdmissionEvidence payment)

------------------------------------------------------------------------
-- Exact current first-missing obligations.
------------------------------------------------------------------------

data CommunityOutcomeConsumerMatchReceiptMissing : Set where
data CurrentCommunityMandateReceiptMissing : Set where

data GenericConsensusCandidateEnoughForPayment : Set where

data GenericRNTBCRoleEnoughForWholeCommunityAuthority : Set where

communityOutcomeConsumerMatchIsStillRequired : Bool
communityOutcomeConsumerMatchIsStillRequired = true

currentCommunityMandateIsStillRequired : Bool
currentCommunityMandateIsStillRequired = true

communityOutcomeConsumerMatchIsStillRequiredExact :
  communityOutcomeConsumerMatchIsStillRequired ≡ true
communityOutcomeConsumerMatchIsStillRequiredExact = refl

currentCommunityMandateIsStillRequiredExact :
  currentCommunityMandateIsStillRequired ≡ true
currentCommunityMandateIsStillRequiredExact = refl

genericConsensusCandidateDoesNotPay : GenericConsensusCandidateEnoughForPayment → ⊥
genericConsensusCandidateDoesNotPay ()

genericRntbcRoleDoesNotPayWholeCommunityAuthority :
  GenericRNTBCRoleEnoughForWholeCommunityAuthority → ⊥
genericRntbcRoleDoesNotPayWholeCommunityAuthority ()

firstResidualBeforePayment :
  Bridge.currentFirstResidualV02 ≡ Bridge.affectedCommunityOutcomeResidualV02
firstResidualBeforePayment = refl

------------------------------------------------------------------------
-- Search scheduler target: do not widen the search until these exact receipts
-- are paid or explicitly shown unavailable for the selected consumer.
------------------------------------------------------------------------

data HighestAlphaNextProducer : Set where
  obtainConsumerMatchedCommunityOutcomeAndMandate
  : HighestAlphaNextProducer

highestAlphaNextProducer : HighestAlphaNextProducer
highestAlphaNextProducer = obtainConsumerMatchedCommunityOutcomeAndMandate

record PaymentCutBoundary : Set where
  constructor payment-cut-boundary
  field
    moreStateStatisticsAreFirstMissing : Bool
    moreStateStatisticsAreFirstMissingIsFalse : moreStateStatisticsAreFirstMissing ≡ false
    anotherGenericOntologyLayerIsFirstMissing : Bool
    anotherGenericOntologyLayerIsFirstMissingIsFalse :
      anotherGenericOntologyLayerIsFirstMissing ≡ false
    consumerMatchedOutcomeReceiptIsRequired : Bool
    consumerMatchedOutcomeReceiptIsRequiredIsTrue : consumerMatchedOutcomeReceiptIsRequired ≡ true
    currentMandateReceiptIsRequired : Bool
    currentMandateReceiptIsRequiredIsTrue : currentMandateReceiptIsRequired ≡ true

canonicalPaymentCutBoundary : PaymentCutBoundary
canonicalPaymentCutBoundary = payment-cut-boundary
  false refl
  false refl
  true refl
  true refl
