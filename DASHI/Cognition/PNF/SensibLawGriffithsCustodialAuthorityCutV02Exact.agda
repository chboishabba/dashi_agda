module DASHI.Cognition.PNF.SensibLawGriffithsCustodialAuthorityCutV02Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawGriffithsCustodialOutcomePaymentV02Exact as Outcome
import DASHI.Cognition.PNF.SensibLawCountryCommunityAuthorityAdmissibilityV02Exact as Authority
import DASHI.Cognition.PNF.SensibLawCountryCommunityPaymentAcquisitionPlanV02Exact as Acquisition
import DASHI.Governance.NativeTitleAuthorityLayerExact as NativeTitle

------------------------------------------------------------------------
-- GRIFFITHS CUSTODIAL AUTHORITY CUT V02
--
-- The High Court source identifies historical proceeding representation
-- (Griffiths deceased / Lorraine Jones on behalf of the Ngaliwurru and Nungali
-- Peoples) and accepted traditional-law custodial evidence.  That does not by
-- itself establish a present mandate for the current operational consumer.
------------------------------------------------------------------------

record HistoricalProceedingRepresentationV02 : Set where
  constructor historical-proceeding-representation-v02
  field
    proceedingReference : String
    representedPeopleReference : String
    representativeReference : String
    representationTemporalEnvelope : String
    representationEvidenceReference : String
    provesPresentCommunityMandate : Bool
    provesPresentCommunityMandateIsFalse : provesPresentCommunityMandate ≡ false

open HistoricalProceedingRepresentationV02 public

griffithsHistoricalRepresentation : HistoricalProceedingRepresentationV02
griffithsHistoricalRepresentation = historical-proceeding-representation-v02
  "Northern Territory v Griffiths (deceased) and Jones on behalf of the Ngaliwurru and Nungali Peoples [2019] HCA 7"
  "Ngaliwurru and Nungali Peoples"
  "Lorraine Jones, as identified in the proceeding title/source"
  "historical litigation representation through the 2019 High Court proceeding"
  "primary High Court source identity; representation title is evidence of proceeding role, not a present community-governance mandate"
  false refl

------------------------------------------------------------------------
-- Narrow current residual after the outcome payment.
------------------------------------------------------------------------

data GriffithsAuthorityResidual : Set where
  presentCustodialMandateResidual
  roleScopeCorrespondenceResidual
  : GriffithsAuthorityResidual

currentGriffithsAuthorityResidual : GriffithsAuthorityResidual
currentGriffithsAuthorityResidual = presentCustodialMandateResidual

currentAuthorityCandidate : Authority.CommunityAuthorityReceiptV02
currentAuthorityCandidate = Authority.traditionalOwnerAuthorityCandidate

currentCandidateRoleIsTraditionalOwnerCommunity :
  Authority.authorityRole currentAuthorityCandidate ≡ NativeTitle.traditionalOwnerCommunity
currentCandidateRoleIsTraditionalOwnerCommunity = refl

historicalRepresentationDoesNotPayPresentMandate :
  provesPresentCommunityMandate griffithsHistoricalRepresentation ≡ false
historicalRepresentationDoesNotPayPresentMandate = refl

outcomeCoordinateAlreadyPaidForNarrowConsumer :
  Outcome.narrowConsumerOutcomePaid Outcome.canonicalGriffithsCustodialOutcomeBoundary ≡ true
outcomeCoordinateAlreadyPaidForNarrowConsumer = refl

------------------------------------------------------------------------
-- The next search is no longer outcome discovery.  It is mandate/role/temporal
-- correspondence for the same custodial consumer.
------------------------------------------------------------------------

nextSearchCoordinate : Acquisition.PaymentCoordinate
nextSearchCoordinate = Acquisition.communityMandateScopeCoordinate

nextSearchProducerExact :
  Acquisition.producerForPaymentCoordinate nextSearchCoordinate
  ≡ DASHI.Law.SensibLawProofDirectedSearchIntentExact.attributionProducer
nextSearchProducerExact = refl

record PresentMandatePaymentV02 : Set₁ where
  constructor present-mandate-payment-v02
  field
    sameCustodialConsumer : Set
    presentAuthorityBearerIdentified : Set
    mandateWithinRoleScope : Set
    mandateValidForCurrentConsumerEnvelope : Set
    provenanceAndDecisionProcessPreserved : Set
    paymentReference : String

------------------------------------------------------------------------
-- No inhabitant is manufactured here.  A historical court representation,
-- RNTBC/PBC role, or source attribution is insufficient by itself.
------------------------------------------------------------------------

data HistoricalRepresentationEqualsCurrentMandate : Set where
data LitigationRepresentativeEqualsWholeCommunityAuthority : Set where
data CourtSourceCreatesPresentCommunityMandate : Set where

data GenericTraditionalOwnerRolePaysSpecificMandate : Set where

historicalRepresentationDoesNotEqualCurrentMandate :
  HistoricalRepresentationEqualsCurrentMandate → ⊥
historicalRepresentationDoesNotEqualCurrentMandate ()

litigationRepresentativeDoesNotEqualWholeCommunityAuthority :
  LitigationRepresentativeEqualsWholeCommunityAuthority → ⊥
litigationRepresentativeDoesNotEqualWholeCommunityAuthority ()

courtSourceDoesNotCreatePresentCommunityMandate :
  CourtSourceCreatesPresentCommunityMandate → ⊥
courtSourceDoesNotCreatePresentCommunityMandate ()

genericTraditionalOwnerRoleDoesNotPaySpecificMandate :
  GenericTraditionalOwnerRolePaysSpecificMandate → ⊥
genericTraditionalOwnerRoleDoesNotPaySpecificMandate ()

record GriffithsAuthorityCutBoundary : Set where
  constructor griffiths-authority-cut-boundary
  field
    narrowOutcomePaid : Bool
    narrowOutcomePaidIsTrue : narrowOutcomePaid ≡ true
    historicalRepresentationMapped : Bool
    historicalRepresentationMappedIsTrue : historicalRepresentationMapped ≡ true
    presentMandatePaid : Bool
    presentMandatePaidIsFalse : presentMandatePaid ≡ false
    nextProducerIsMandateAttribution : Bool
    nextProducerIsMandateAttributionIsTrue : nextProducerIsMandateAttribution ≡ true

canonicalGriffithsAuthorityCutBoundary : GriffithsAuthorityCutBoundary
canonicalGriffithsAuthorityCutBoundary = griffiths-authority-cut-boundary
  true refl
  true refl
  false refl
  true refl
