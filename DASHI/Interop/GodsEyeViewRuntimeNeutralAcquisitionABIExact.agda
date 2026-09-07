module DASHI.Interop.GodsEyeViewRuntimeNeutralAcquisitionABIExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.GodsEyeViewHighestAlphaObservationChoiceExact as Alpha

------------------------------------------------------------------------
-- RUNTIME-NEUTRAL WORLD ACQUISITION ABI
--
-- The GEV/world-research loop chooses a consumer-relative observation/source
-- move.  Provider implementations may then be legal-source fetchers, sensors,
-- market-data clients, Wikidata reference verifiers, community-source
-- acquisition, or local archive/runtime readers.  This ABI preserves those
-- differences without allowing provider success to become semantic payment.
------------------------------------------------------------------------

data AcquisitionProviderKind : Set where
  documentSourceProvider : AcquisitionProviderKind
  sensorObservationProvider : AcquisitionProviderKind
  marketDataProvider : AcquisitionProviderKind
  wikimediaReferenceProvider : AcquisitionProviderKind
  communitySourceProvider : AcquisitionProviderKind
  localArchiveProvider : AcquisitionProviderKind
  runtimeGeneratedProvider : AcquisitionProviderKind

data AcquisitionCarrierKind : Set where
  attributedDocumentCarrier : AcquisitionCarrierKind
  calibratedSensorCarrier : AcquisitionCarrierKind
  marketEventCarrier : AcquisitionCarrierKind
  wikimediaReferenceCarrier : AcquisitionCarrierKind
  communityKnowledgeCarrier : AcquisitionCarrierKind
  archiveContentCarrier : AcquisitionCarrierKind
  runtimeReceiptCarrier : AcquisitionCarrierKind

data AcquisitionExecutionStatus : Set where
  executedWithOutput : AcquisitionExecutionStatus
  executedNoMatch : AcquisitionExecutionStatus
  blockedBeforeExecution : AcquisitionExecutionStatus
  providerUnavailable : AcquisitionExecutionStatus
  executionFailed : AcquisitionExecutionStatus

record RuntimeNeutralAcquisitionRequest : Set₁ where
  constructor runtime-neutral-acquisition-request
  field
    selectedCandidate : Alpha.HighestAlphaCandidate
    providerKind : AcquisitionProviderKind
    requestedCarrier : AcquisitionCarrierKind
    consumerReference : String
    exactPrerequisiteReference : String
    requestedCoordinateReference : String
    boundedScopeReference : String
    authorityReference : String
    privacyMinimisationReference : String
    budgetReference : String
    requestIdentityReference : String

open RuntimeNeutralAcquisitionRequest public

record RuntimeNeutralAcquisitionResult
    (request : RuntimeNeutralAcquisitionRequest) : Set₁ where
  constructor runtime-neutral-acquisition-result
  field
    executionStatus : AcquisitionExecutionStatus
    providerExecutionReference : String
    returnedCarrier : AcquisitionCarrierKind
    carrierMatchesRequestReference : String
    sourceOrInstrumentReference : String
    sourceRevisionOrObservationTimeReference : String
    exactLocatorOrCoordinateReference : String
    contentIdentityOrHashReference : String
    coverageReference : String
    uncertaintyReference : String
    provenanceReference : String
    acquisitionAuthorityReference : String
    rawEvidenceReference : String
    providerSemanticInterpretationReference : String
    providerCreatesTruth : Bool
    providerCreatesTruthIsFalse : providerCreatesTruth ≡ false
    providerCreatesApplicability : Bool
    providerCreatesApplicabilityIsFalse : providerCreatesApplicability ≡ false
    providerCreatesInterventionAuthority : Bool
    providerCreatesInterventionAuthorityIsFalse :
      providerCreatesInterventionAuthority ≡ false
    resultIdentityReference : String

open RuntimeNeutralAcquisitionResult public

------------------------------------------------------------------------
-- Provider/carrier calibration fixtures.
-- These classify transport shape only; they are not empirical observations.
------------------------------------------------------------------------

providerDefaultCarrier : AcquisitionProviderKind → AcquisitionCarrierKind
providerDefaultCarrier documentSourceProvider = attributedDocumentCarrier
providerDefaultCarrier sensorObservationProvider = calibratedSensorCarrier
providerDefaultCarrier marketDataProvider = marketEventCarrier
providerDefaultCarrier wikimediaReferenceProvider = wikimediaReferenceCarrier
providerDefaultCarrier communitySourceProvider = communityKnowledgeCarrier
providerDefaultCarrier localArchiveProvider = archiveContentCarrier
providerDefaultCarrier runtimeGeneratedProvider = runtimeReceiptCarrier

documentProviderCarrierRegression :
  providerDefaultCarrier documentSourceProvider ≡ attributedDocumentCarrier
documentProviderCarrierRegression = refl

sensorProviderCarrierRegression :
  providerDefaultCarrier sensorObservationProvider ≡ calibratedSensorCarrier
sensorProviderCarrierRegression = refl

marketProviderCarrierRegression :
  providerDefaultCarrier marketDataProvider ≡ marketEventCarrier
marketProviderCarrierRegression = refl

wikimediaProviderCarrierRegression :
  providerDefaultCarrier wikimediaReferenceProvider ≡ wikimediaReferenceCarrier
wikimediaProviderCarrierRegression = refl

communityProviderCarrierRegression :
  providerDefaultCarrier communitySourceProvider ≡ communityKnowledgeCarrier
communityProviderCarrierRegression = refl

------------------------------------------------------------------------
-- Fail-closed runtime boundaries.
------------------------------------------------------------------------

data ExecutedWithOutputAutomaticallyPaysPrerequisite : Set where
data ContentHashAutomaticallyProvesSameObject : Set where
data ProviderSuccessAutomaticallyCreatesSourceSupport : Set where
data SensorObservationAutomaticallyAuthorisesIntervention : Set where
data CommunitySourceAutomaticallyTransfersCommunityAuthority : Set where
data WikimediaReferenceAutomaticallyVerifiesExternalDocument : Set where

executionSuccessDoesNotPayPrerequisite :
  ExecutedWithOutputAutomaticallyPaysPrerequisite → ⊥
executionSuccessDoesNotPayPrerequisite ()

contentHashDoesNotByItselfProveSameObject :
  ContentHashAutomaticallyProvesSameObject → ⊥
contentHashDoesNotByItselfProveSameObject ()

providerSuccessDoesNotCreateSourceSupport :
  ProviderSuccessAutomaticallyCreatesSourceSupport → ⊥
providerSuccessDoesNotCreateSourceSupport ()

sensorObservationDoesNotAuthoriseIntervention :
  SensorObservationAutomaticallyAuthorisesIntervention → ⊥
sensorObservationDoesNotAuthoriseIntervention ()

communitySourceDoesNotTransferAuthority :
  CommunitySourceAutomaticallyTransfersCommunityAuthority → ⊥
communitySourceDoesNotTransferAuthority ()

wikimediaReferenceDoesNotVerifyExternalDocument :
  WikimediaReferenceAutomaticallyVerifiesExternalDocument → ⊥
wikimediaReferenceDoesNotVerifyExternalDocument ()

record RuntimeNeutralAcquisitionBoundary : Set where
  constructor runtime-neutral-acquisition-boundary
  field
    providerKindsRemainDistinct : Bool
    providerKindsRemainDistinctIsTrue : providerKindsRemainDistinct ≡ true
    carrierKindsRemainDistinct : Bool
    carrierKindsRemainDistinctIsTrue : carrierKindsRemainDistinct ≡ true
    executionStatusIsNotSemanticPayment : Bool
    executionStatusIsNotSemanticPaymentIsTrue : executionStatusIsNotSemanticPayment ≡ true
    resultRetainsRevisionCoverageAndProvenance : Bool
    resultRetainsRevisionCoverageAndProvenanceIsTrue :
      resultRetainsRevisionCoverageAndProvenance ≡ true
    downstreamAuthorityRemainsSeparate : Bool
    downstreamAuthorityRemainsSeparateIsTrue : downstreamAuthorityRemainsSeparate ≡ true

canonicalRuntimeNeutralAcquisitionBoundary : RuntimeNeutralAcquisitionBoundary
canonicalRuntimeNeutralAcquisitionBoundary =
  runtime-neutral-acquisition-boundary true refl true refl true refl true refl true refl
