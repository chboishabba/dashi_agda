module DASHI.Interop.GodsEyeViewP854InspectionWorldAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.GodsEyeViewRuntimeNeutralAcquisitionABIExact as ABI
import DASHI.Interop.GodsEyeViewAcquisitionResultAssessmentBridgeExact as Assessment

------------------------------------------------------------------------
-- P854 EXTERNAL-REFERENCE INSPECTION -> WORLD ACQUISITION ABI
--
-- This is deliberately a transport adapter, not another source ontology and
-- not another return classifier.  Native P854 classification / source-candidate
-- semantics remain owned by the Wikimedia/SLR lane (#814 / SLR #10).  This owner
-- states only the compatibility surface required by the GEV runtime-neutral
-- world loop once that external inspection has returned.
--
-- The request must already be bound to the exact live consumer/prerequisite/
-- coordinate selected upstream.  A URL string by itself is therefore not an
-- admissible world-research result.
------------------------------------------------------------------------

record BoundP854WorldRequest
    (request : ABI.RuntimeNeutralAcquisitionRequest) : Set where
  constructor bound-p854-world-request
  field
    providerIsWikimediaReference :
      ABI.providerKind request ≡ ABI.wikimediaReferenceProvider
    requestedCarrierIsWikimediaReference :
      ABI.requestedCarrier request ≡ ABI.wikimediaReferenceCarrier
    nativeStatementReference : String
    p854ReferenceURL : String
    bindingReference : String

open BoundP854WorldRequest public

data P854InspectionOutcome : Set where
  inspectedSameReferenceURL : P854InspectionOutcome
  executedNoReferenceMatch : P854InspectionOutcome
  inspectionBlocked : P854InspectionOutcome
  inspectionProviderUnavailable : P854InspectionOutcome
  inspectionFailed : P854InspectionOutcome

executionStatusFor : P854InspectionOutcome → ABI.AcquisitionExecutionStatus
executionStatusFor inspectedSameReferenceURL = ABI.executedWithOutput
executionStatusFor executedNoReferenceMatch = ABI.executedNoMatch
executionStatusFor inspectionBlocked = ABI.blockedBeforeExecution
executionStatusFor inspectionProviderUnavailable = ABI.providerUnavailable
executionStatusFor inspectionFailed = ABI.executionFailed

p854OutcomeAllowsSemanticAssessment : P854InspectionOutcome → Bool
p854OutcomeAllowsSemanticAssessment inspectedSameReferenceURL = true
p854OutcomeAllowsSemanticAssessment executedNoReferenceMatch = false
p854OutcomeAllowsSemanticAssessment inspectionBlocked = false
p854OutcomeAllowsSemanticAssessment inspectionProviderUnavailable = false
p854OutcomeAllowsSemanticAssessment inspectionFailed = false

-- Exact compatibility with the existing generic admission classifier.  This is
-- the key no-duplication theorem: the P854 adapter does not own a second notion
-- of whether a runtime result may enter semantic assessment.
genericAssessmentAdmissionAgrees :
  (outcome : P854InspectionOutcome) →
  Assessment.executionAllowsSemanticAssessment (executionStatusFor outcome)
  ≡ p854OutcomeAllowsSemanticAssessment outcome
genericAssessmentAdmissionAgrees inspectedSameReferenceURL = refl
genericAssessmentAdmissionAgrees executedNoReferenceMatch = refl
genericAssessmentAdmissionAgrees inspectionBlocked = refl
genericAssessmentAdmissionAgrees inspectionProviderUnavailable = refl
genericAssessmentAdmissionAgrees inspectionFailed = refl

record P854WorldInspectionReceipt
    {request : ABI.RuntimeNeutralAcquisitionRequest}
    (bound : BoundP854WorldRequest request) : Set₁ where
  constructor p854-world-inspection-receipt
  field
    outcome : P854InspectionOutcome
    providerExecutionReference : String
    sourceRevisionOrObservationTimeReference : String
    exactLocatorReference : String
    contentIdentityOrHashReference : String
    coverageReference : String
    uncertaintyReference : String
    provenanceReference : String
    acquisitionAuthorityReference : String
    rawEvidenceReference : String
    resultIdentityReference : String
    inspectionReference : String

open P854WorldInspectionReceipt public

p854ReceiptToRuntimeResult :
  ∀ {request}
    {bound : BoundP854WorldRequest request} →
  P854WorldInspectionReceipt bound →
  ABI.RuntimeNeutralAcquisitionResult request
p854ReceiptToRuntimeResult {bound = bound} receipt =
  ABI.runtime-neutral-acquisition-result
    (executionStatusFor (outcome receipt))
    (providerExecutionReference receipt)
    ABI.wikimediaReferenceCarrier
    "P854 adapter returns the Wikimedia reference carrier required by the bound request"
    (p854ReferenceURL bound)
    (sourceRevisionOrObservationTimeReference receipt)
    (exactLocatorReference receipt)
    (contentIdentityOrHashReference receipt)
    (coverageReference receipt)
    (uncertaintyReference receipt)
    (provenanceReference receipt)
    (acquisitionAuthorityReference receipt)
    (rawEvidenceReference receipt)
    (inspectionReference receipt)
    false refl
    false refl
    false refl
    (resultIdentityReference receipt)

------------------------------------------------------------------------
-- Introspective firewalls.
------------------------------------------------------------------------

data P854PresencePaysSourceSupport : Set where
data P854FetchPaysSourceSupport : Set where
data P854InspectionPaysSourceSupport : Set where
data P854NoMatchMeansPropositionFalse : Set where
data P854RuntimeResultCreatesApplicability : Set where
data P854RuntimeResultCreatesInterventionAuthority : Set where

p854PresenceDoesNotPaySourceSupport : P854PresencePaysSourceSupport → ⊥
p854PresenceDoesNotPaySourceSupport ()

p854FetchDoesNotPaySourceSupport : P854FetchPaysSourceSupport → ⊥
p854FetchDoesNotPaySourceSupport ()

p854InspectionDoesNotPaySourceSupport : P854InspectionPaysSourceSupport → ⊥
p854InspectionDoesNotPaySourceSupport ()

p854NoMatchDoesNotMeanPropositionFalse : P854NoMatchMeansPropositionFalse → ⊥
p854NoMatchDoesNotMeanPropositionFalse ()

p854RuntimeResultDoesNotCreateApplicability :
  P854RuntimeResultCreatesApplicability → ⊥
p854RuntimeResultDoesNotCreateApplicability ()

p854RuntimeResultDoesNotCreateInterventionAuthority :
  P854RuntimeResultCreatesInterventionAuthority → ⊥
p854RuntimeResultDoesNotCreateInterventionAuthority ()

------------------------------------------------------------------------
-- Boundary receipt.
------------------------------------------------------------------------

record P854WorldAdapterBoundary : Set where
  constructor p854-world-adapter-boundary
  field
    requestMustRemainLiveResidualBound : Bool
    requestMustRemainLiveResidualBoundIsTrue :
      requestMustRemainLiveResidualBound ≡ true
    inspectedSameURLMayEnterGenericAssessment : Bool
    inspectedSameURLMayEnterGenericAssessmentIsTrue :
      inspectedSameURLMayEnterGenericAssessment ≡ true
    noMatchMayEnterGenericAssessment : Bool
    noMatchMayEnterGenericAssessmentIsFalse :
      noMatchMayEnterGenericAssessment ≡ false
    adapterOwnsSemanticDisposition : Bool
    adapterOwnsSemanticDispositionIsFalse :
      adapterOwnsSemanticDisposition ≡ false
    adapterCreatesSourceSupport : Bool
    adapterCreatesSourceSupportIsFalse :
      adapterCreatesSourceSupport ≡ false

canonicalP854WorldAdapterBoundary : P854WorldAdapterBoundary
canonicalP854WorldAdapterBoundary =
  p854-world-adapter-boundary true refl true refl false refl false refl false refl
