module DASHI.Culture.LinguisticAnthropologyCommunicativeEventPaymentReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Culture.LinguisticAnthropologyTlureyPragmaticsBridgeExact as LA

------------------------------------------------------------------------
-- RECEIPT-INDEXED COMMUNICATIVE EVENT PAYMENT
--
-- Cross-pollinated from the same-object / receipt-indexed patterns used by
-- recent DASHI scientific-wall and runtime-observation work:
--
--   acquisition != payment
--   all-true status flags != evidence
--   terminal closure requires exact receipts welded to the same object
--   source/runtime revisions remain explicit coordinates
--
-- For linguistic anthropology, the exact object is one communicative event.
-- A transcript, participant/context note, authority/standing note and analytic
-- interpretation may all be acquired independently and retained out of order,
-- but they only pay the event when they bind to the same event identity.
------------------------------------------------------------------------

record CommunicativeEventIdentity : Set where
  constructor communicative-event-identity
  field
    eventId : String
    communityOrField : String
    place : String
    eventTime : String
    corpusRevision : String
    transcriptionRevision : String
open CommunicativeEventIdentity public

record SpeechCarrierReceipt : Set where
  constructor speech-carrier-receipt
  field
    event : CommunicativeEventIdentity
    carrierReference : String
    carrierKind : String
    sourceDigest : String
    languageOrVariety : String
    transcriptReference : String
    transcriptRevision : String
    tokenOrSegmentReference : String
    sourceProvenance : String
open SpeechCarrierReceipt public

record ParticipantContextReceipt : Set where
  constructor participant-context-receipt
  field
    event : CommunicativeEventIdentity
    speakerReference : String
    participantReference : String
    activityReference : String
    localTermsReference : String
    relationHistoryReference : String
    fieldworkReference : String
    observerPositionReference : String
open ParticipantContextReceipt public

record StandingPermissionReceipt : Set where
  constructor standing-permission-receipt
  field
    event : CommunicativeEventIdentity
    speakerStandingReference : String
    disclosurePermissionReference : String
    interpretiveObligationReference : String
    consentOrAuthorityReference : String
    restrictedMaterialBoundary : String
open StandingPermissionReceipt public

record InteractionalAnalysisReceipt : Set where
  constructor interactional-analysis-receipt
  field
    event : CommunicativeEventIdentity
    analysisReference : String
    analyticRevision : String
    contextualReading : String
    interactionalEffect : String
    localInterpretationReference : String
    researcherInterpretationReference : String
    sourceTheoryReference : String
    alternativeReadingRetained : Bool
open InteractionalAnalysisReceipt public

------------------------------------------------------------------------
-- Acquisition state is deliberately weaker than payment.
------------------------------------------------------------------------

record CommunicativeEventAcquisitionState : Set where
  constructor communicative-event-acquisition-state
  field
    speechCarrierAcquired : Bool
    participantContextAcquired : Bool
    standingPermissionAcquired : Bool
    interactionalAnalysisAcquired : Bool
open CommunicativeEventAcquisitionState public

record CommunicativeEventPaymentState : Set where
  constructor communicative-event-payment-state
  field
    speechCarrierPaid : Bool
    participantContextPaid : Bool
    standingPermissionPaid : Bool
    interactionalAnalysisPaid : Bool
open CommunicativeEventPaymentState public

outOfOrderAcquisition : CommunicativeEventAcquisitionState
outOfOrderAcquisition = communicative-event-acquisition-state true true false true

noPaymentFromAcquisitionAlone : CommunicativeEventPaymentState
noPaymentFromAcquisitionAlone = communicative-event-payment-state false false false false

------------------------------------------------------------------------
-- Terminal payment requires same-object welds.
------------------------------------------------------------------------

record FullyPaidCommunicativeEventReceipt : Set where
  constructor fully-paid-communicative-event-receipt
  field
    speech : SpeechCarrierReceipt
    context : ParticipantContextReceipt
    governance : StandingPermissionReceipt
    analysis : InteractionalAnalysisReceipt

    contextUsesSameEvent : event context ≡ event speech
    governanceUsesSameEvent : event governance ≡ event speech
    analysisUsesSameEvent : event analysis ≡ event speech

    situatedEvent : LA.SituatedSpeechEvent
    situatedWordsReference : String
    situatedEventCompiledFromSameSpeech : Bool
    situatedEventCompiledFromSameContext : Bool
    situatedEventCompiledFromSameGovernance : Bool
    situatedEventCompiledFromSameAnalysis : Bool

    sourceTraditionsRetained : Bool
    empiricalPromotionAllowed : Bool
open FullyPaidCommunicativeEventReceipt public

paymentStateFromReceipt : FullyPaidCommunicativeEventReceipt → CommunicativeEventPaymentState
paymentStateFromReceipt _ = communicative-event-payment-state true true true true

------------------------------------------------------------------------
-- Minimal consumer: a real linguistic-anthropology producer is one exact
-- event payment.  A corpus/community producer may aggregate many such receipts
-- later, but aggregation is not a prerequisite for this event-level consumer.
------------------------------------------------------------------------

record CommunicativeEventProducerFrontier : Set where
  constructor communicative-event-producer-frontier
  field
    receiptShapePaid : Bool
    sameObjectWeldPaid : Bool
    revisionBindingPaid : Bool
    concreteSpeechCarrierPaid : Bool
    concreteParticipantContextPaid : Bool
    concreteStandingPermissionPaid : Bool
    concreteInteractionalAnalysisPaid : Bool
    firstConcreteEventPaid : Bool
    wholeCorpusRequiredBeforeFirstEvent : Bool
open CommunicativeEventProducerFrontier public

currentCommunicativeEventFrontier : CommunicativeEventProducerFrontier
currentCommunicativeEventFrontier =
  communicative-event-producer-frontier
    true true true false false false false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data AcquisitionCreatesPayment : Set where
data TranscriptCreatesContext : Set where
data TranscriptCreatesStanding : Set where
data SameWordsCreateSameEvent : Set where
data AnalysisCreatesObservation : Set where
data NeighbourEventContextTransfers : Set where
data AllTrueFlagsCreateEmpiricalReceipt : Set where

acquisitionDoesNotCreatePayment : AcquisitionCreatesPayment → ⊥
acquisitionDoesNotCreatePayment ()

transcriptDoesNotCreateContext : TranscriptCreatesContext → ⊥
transcriptDoesNotCreateContext ()

transcriptDoesNotCreateStanding : TranscriptCreatesStanding → ⊥
transcriptDoesNotCreateStanding ()

sameWordsDoNotCreateSameEvent : SameWordsCreateSameEvent → ⊥
sameWordsDoNotCreateSameEvent ()

analysisDoesNotCreateObservation : AnalysisCreatesObservation → ⊥
analysisDoesNotCreateObservation ()

neighbourEventContextDoesNotTransfer : NeighbourEventContextTransfers → ⊥
neighbourEventContextDoesNotTransfer ()

allTrueFlagsDoNotCreateEmpiricalReceipt : AllTrueFlagsCreateEmpiricalReceipt → ⊥
allTrueFlagsDoNotCreateEmpiricalReceipt ()

record CommunicativeEventPaymentBoundary : Set where
  constructor communicative-event-payment-boundary
  field
    acquisitionAndPaymentSeparate : Bool
    terminalPaymentRequiresReceipts : Bool
    allReceiptsMustBindSameEvent : Bool
    revisionCoordinatesExplicit : Bool
    transcriptDeterminesStanding : Bool
    formalTlureyContextDeterminesCommunityMeaning : Bool
    wholeCorpusRequiredForEventPayment : Bool
open CommunicativeEventPaymentBoundary public

canonicalCommunicativeEventPaymentBoundary : CommunicativeEventPaymentBoundary
canonicalCommunicativeEventPaymentBoundary =
  communicative-event-payment-boundary true true true true false false false
