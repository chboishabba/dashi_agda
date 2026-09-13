module DASHI.Interop.GodsEyeViewCommunitySourceWorldAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.GodsEyeViewRuntimeNeutralAcquisitionABIExact as ABI
import DASHI.Interop.GodsEyeViewAcquisitionResultAssessmentBridgeExact as Assessment

------------------------------------------------------------------------
-- COMMUNITY-SOURCE / AUTHORITY ACQUISITION -> WORLD ACQUISITION ABI
--
-- A community-originating source may evidence a community-defined outcome,
-- history, position, mandate, or correction.  Merely receiving such a source
-- does not transfer community authority to the runtime and does not prove that
-- the speaker/source holds the exact mandate required by the live consumer.
------------------------------------------------------------------------

record BoundCommunitySourceWorldRequest
    (request : ABI.RuntimeNeutralAcquisitionRequest) : Set where
  constructor bound-community-source-world-request
  field
    providerIsCommunitySource :
      ABI.providerKind request ≡ ABI.communitySourceProvider
    requestedCarrierIsCommunityKnowledge :
      ABI.requestedCarrier request ≡ ABI.communityKnowledgeCarrier

    communityReference : String
    affectedConsumerReference : String
    communityDefinedOutcomeReference : String
    requestedMandateScopeReference : String
    requestedRoleReference : String
    requestedTemporalEnvelopeReference : String
    requestedCountryOrPlaceReference : String
    consentOrAccessAuthorityReference : String
    provenanceExpectationReference : String
    contraryOrDissentSourceExpectationReference : String
    correctionChannelReference : String
    bindingReference : String

open BoundCommunitySourceWorldRequest public

data CommunitySourceAcquisitionOutcome : Set where
  executedWithCommunitySource : CommunitySourceAcquisitionOutcome
  executedNoCommunitySourceMatch : CommunitySourceAcquisitionOutcome
  communityAcquisitionBlocked : CommunitySourceAcquisitionOutcome
  communityProviderUnavailable : CommunitySourceAcquisitionOutcome
  communityAcquisitionFailed : CommunitySourceAcquisitionOutcome

executionStatusFor : CommunitySourceAcquisitionOutcome → ABI.AcquisitionExecutionStatus
executionStatusFor executedWithCommunitySource = ABI.executedWithOutput
executionStatusFor executedNoCommunitySourceMatch = ABI.executedNoMatch
executionStatusFor communityAcquisitionBlocked = ABI.blockedBeforeExecution
executionStatusFor communityProviderUnavailable = ABI.providerUnavailable
executionStatusFor communityAcquisitionFailed = ABI.executionFailed

communityOutcomeAllowsSemanticAssessment : CommunitySourceAcquisitionOutcome → Bool
communityOutcomeAllowsSemanticAssessment executedWithCommunitySource = true
communityOutcomeAllowsSemanticAssessment executedNoCommunitySourceMatch = false
communityOutcomeAllowsSemanticAssessment communityAcquisitionBlocked = false
communityOutcomeAllowsSemanticAssessment communityProviderUnavailable = false
communityOutcomeAllowsSemanticAssessment communityAcquisitionFailed = false

genericAssessmentAdmissionAgrees :
  (outcome : CommunitySourceAcquisitionOutcome) →
  Assessment.executionAllowsSemanticAssessment (executionStatusFor outcome)
  ≡ communityOutcomeAllowsSemanticAssessment outcome
genericAssessmentAdmissionAgrees executedWithCommunitySource = refl
genericAssessmentAdmissionAgrees executedNoCommunitySourceMatch = refl
genericAssessmentAdmissionAgrees communityAcquisitionBlocked = refl
genericAssessmentAdmissionAgrees communityProviderUnavailable = refl
genericAssessmentAdmissionAgrees communityAcquisitionFailed = refl

record CommunitySourceWorldAcquisitionReceipt
    {request : ABI.RuntimeNeutralAcquisitionRequest}
    (bound : BoundCommunitySourceWorldRequest request) : Set₁ where
  constructor community-source-world-acquisition-receipt
  field
    outcome : CommunitySourceAcquisitionOutcome
    providerExecutionReference : String
    sourceRevisionOrObservationTimeReference : String
    exactLocatorReference : String
    contentIdentityOrHashReference : String
    coverageReference : String
    uncertaintyReference : String
    provenanceReference : String
    acquisitionAuthorityReference : String
    rawEvidenceReference : String
    providerInterpretationReference : String
    resultIdentityReference : String

    speakerOrResponsibleBodyReference : String
    roleAssessmentReference : String
    mandateScopeAssessmentReference : String
    temporalValidityAssessmentReference : String
    sameConsumerOutcomeAssessmentReference : String
    consentOrAccessAssessmentReference : String
    dissentOrContrarySourceAssessmentReference : String
    correctionChannelAssessmentReference : String

open CommunitySourceWorldAcquisitionReceipt public

communityReceiptToRuntimeResult :
  ∀ {request}
    {bound : BoundCommunitySourceWorldRequest request} →
  CommunitySourceWorldAcquisitionReceipt bound →
  ABI.RuntimeNeutralAcquisitionResult request
communityReceiptToRuntimeResult {bound = bound} receipt =
  ABI.runtime-neutral-acquisition-result
    (executionStatusFor (outcome receipt))
    (providerExecutionReference receipt)
    ABI.communityKnowledgeCarrier
    "community-source adapter returns the community-knowledge carrier required by the bound request"
    (communityReference bound)
    (sourceRevisionOrObservationTimeReference receipt)
    (exactLocatorReference receipt)
    (contentIdentityOrHashReference receipt)
    (coverageReference receipt)
    (uncertaintyReference receipt)
    (provenanceReference receipt)
    (acquisitionAuthorityReference receipt)
    (rawEvidenceReference receipt)
    (providerInterpretationReference receipt)
    false refl
    false refl
    false refl
    (resultIdentityReference receipt)

------------------------------------------------------------------------
-- Introspective firewalls.
------------------------------------------------------------------------

data CommunitySourceTransfersCommunityAuthority : Set where
data CommunityOriginProvesCurrentMandate : Set where
data ConsultationProvesCommunityDefinedOutcome : Set where
data StateReportExhaustsCommunityOutcome : Set where
data SharedObservationFusesKnowledgeHistory : Set where
data CommunitySourceErasesDissent : Set where
data NoCommunityMatchMeansNoCommunityPosition : Set where

data CommunityAuthorityCreatesUnboundedInterventionAuthority : Set where

communitySourceDoesNotTransferAuthority :
  CommunitySourceTransfersCommunityAuthority → ⊥
communitySourceDoesNotTransferAuthority ()

communityOriginDoesNotProveCurrentMandate :
  CommunityOriginProvesCurrentMandate → ⊥
communityOriginDoesNotProveCurrentMandate ()

consultationDoesNotProveCommunityDefinedOutcome :
  ConsultationProvesCommunityDefinedOutcome → ⊥
consultationDoesNotProveCommunityDefinedOutcome ()

stateReportDoesNotExhaustCommunityOutcome :
  StateReportExhaustsCommunityOutcome → ⊥
stateReportDoesNotExhaustCommunityOutcome ()

sharedObservationDoesNotFuseKnowledgeHistory :
  SharedObservationFusesKnowledgeHistory → ⊥
sharedObservationDoesNotFuseKnowledgeHistory ()

communitySourceDoesNotEraseDissent : CommunitySourceErasesDissent → ⊥
communitySourceDoesNotEraseDissent ()

noCommunityMatchDoesNotMeanNoCommunityPosition :
  NoCommunityMatchMeansNoCommunityPosition → ⊥
noCommunityMatchDoesNotMeanNoCommunityPosition ()

communityAuthorityDoesNotCreateUnboundedInterventionAuthority :
  CommunityAuthorityCreatesUnboundedInterventionAuthority → ⊥
communityAuthorityDoesNotCreateUnboundedInterventionAuthority ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record CommunitySourceWorldAdapterBoundary : Set where
  constructor community-source-world-adapter-boundary
  field
    requestMustRemainLiveResidualBound : Bool
    requestMustRemainLiveResidualBoundIsTrue :
      requestMustRemainLiveResidualBound ≡ true
    consumerOutcomeMandateAndTimeRemainBoundTogether : Bool
    consumerOutcomeMandateAndTimeRemainBoundTogetherIsTrue :
      consumerOutcomeMandateAndTimeRemainBoundTogether ≡ true
    communitySourceAndCommunityAuthorityRemainDistinct : Bool
    communitySourceAndCommunityAuthorityRemainDistinctIsTrue :
      communitySourceAndCommunityAuthorityRemainDistinct ≡ true
    dissentAndCorrectionRemainVisible : Bool
    dissentAndCorrectionRemainVisibleIsTrue :
      dissentAndCorrectionRemainVisible ≡ true
    executedOutputMayEnterGenericAssessment : Bool
    executedOutputMayEnterGenericAssessmentIsTrue :
      executedOutputMayEnterGenericAssessment ≡ true
    noMatchMayEnterGenericAssessment : Bool
    noMatchMayEnterGenericAssessmentIsFalse :
      noMatchMayEnterGenericAssessment ≡ false
    adapterOwnsSemanticDisposition : Bool
    adapterOwnsSemanticDispositionIsFalse :
      adapterOwnsSemanticDisposition ≡ false
    adapterTransfersCommunityAuthority : Bool
    adapterTransfersCommunityAuthorityIsFalse :
      adapterTransfersCommunityAuthority ≡ false

canonicalCommunitySourceWorldAdapterBoundary : CommunitySourceWorldAdapterBoundary
canonicalCommunitySourceWorldAdapterBoundary =
  community-source-world-adapter-boundary
    true refl true refl true refl true refl true refl false refl false refl false refl
