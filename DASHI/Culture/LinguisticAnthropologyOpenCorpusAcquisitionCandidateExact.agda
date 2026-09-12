module DASHI.Culture.LinguisticAnthropologyOpenCorpusAcquisitionCandidateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- OPEN-CORPUS ACQUISITION CANDIDATE
--
-- Candidate corpus:
-- John W. Du Bois, Wallace L. Chafe, Charles Meyer, Sandra A. Thompson,
-- Robert Englebretson et al., Santa Barbara Corpus of Spoken American English
-- (2000-2005).
--
-- Public corpus descriptions report naturally occurring American-English
-- interaction, linked transcripts/audio, and roughly sixty recordings.
--
-- This module is an ACQUISITION candidate only.  It deliberately does not
-- reproduce transcript/audio content and does not claim that public
-- availability establishes unrestricted reuse or that any particular event has
-- already been acquired on the exact revision used by DASHI.
------------------------------------------------------------------------

data CorpusRightsStatus : Set where
  rightsUnresolved : CorpusRightsStatus
  useTermsInspected : CorpusRightsStatus
  exactEventUseAuthorised : CorpusRightsStatus

data EventAcquisitionStatus : Set where
  eventUnselected : EventAcquisitionStatus
  eventSelectedMetadataOnly : EventAcquisitionStatus
  eventTranscriptAcquired : EventAcquisitionStatus
  eventTranscriptAndMediaAcquired : EventAcquisitionStatus
  eventContextBound : EventAcquisitionStatus
  eventReadyForPayment : EventAcquisitionStatus

record LinguisticAnthropologyCorpusCandidate : Set where
  constructor linguistic-anthropology-corpus-candidate
  field
    corpusTitle : String
    creatorReference : String
    corpusDateRange : String
    publicDescriptionReference : String
    interactionType : String
    transcriptAvailable : Bool
    mediaAvailable : Bool
    participantContextAdvertised : Bool
    corpusRevisionReference : String
    rightsReference : String
    rightsStatus : CorpusRightsStatus
    selectedEventReference : String
    eventStatus : EventAcquisitionStatus
open LinguisticAnthropologyCorpusCandidate public

santaBarbaraSpokenAmericanEnglishCandidate : LinguisticAnthropologyCorpusCandidate
santaBarbaraSpokenAmericanEnglishCandidate =
  linguistic-anthropology-corpus-candidate
    "Santa Barbara Corpus of Spoken American English"
    "Du Bois; Chafe; Meyer; Thompson; Englebretson et al."
    "2000-2005 publication series; recordings largely collected in the 1990s"
    "UCSB/TalkBank corpus documentation; scholarly corpus descriptions"
    "naturally occurring spoken interaction, including face-to-face conversation"
    true
    true
    true
    "exact downloaded corpus snapshot not yet bound in this tranche"
    "live corpus/data-use terms must be inspected before event material is retained or redistributed"
    rightsUnresolved
    "no exact conversation selected from the live source yet"
    eventUnselected

------------------------------------------------------------------------
-- Admission gate: public discovery is not event payment.
------------------------------------------------------------------------

record CorpusEventAcquisitionReceipt : Set where
  constructor corpus-event-acquisition-receipt
  field
    candidate : LinguisticAnthropologyCorpusCandidate
    exactEventReference : String
    exactTranscriptReference : String
    exactMediaReference : String
    exactContextReference : String
    corpusSnapshotRevision : String
    transcriptDigest : String
    mediaDigest : String
    participantMetadataReference : String
    permittedUseReference : String
    redistributionBoundary : String
    exactEventRightsBound : Bool
    exactEventContextBound : Bool
    readyForCommunicativeEventPayment : Bool
open CorpusEventAcquisitionReceipt public

record OpenCorpusAcquisitionFrontier : Set where
  constructor open-corpus-acquisition-frontier
  field
    candidateIdentified : Bool
    corpusHasTranscriptSurface : Bool
    corpusHasMediaSurface : Bool
    exactCorpusSnapshotBound : Bool
    liveRightsTermsBound : Bool
    exactEventSelected : Bool
    exactEventTranscriptBound : Bool
    exactEventMediaBound : Bool
    exactEventContextBound : Bool
    eventReadyForPayment : Bool
open OpenCorpusAcquisitionFrontier public

currentOpenCorpusAcquisitionFrontier : OpenCorpusAcquisitionFrontier
currentOpenCorpusAcquisitionFrontier =
  open-corpus-acquisition-frontier
    true true true false false false false false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PublicCorpusCreatesReuseAuthority : Set where
data CorpusDescriptionCreatesEventReceipt : Set where
data TranscriptAvailabilityCreatesTranscriptAcquisition : Set where
data MediaAvailabilityCreatesMediaAcquisition : Set where
data CorpusLevelTermsAutomaticallyBindEveryEvent : Set where

data CorpusCandidateCreatesLinguisticFinding : Set where

publicCorpusDoesNotCreateReuseAuthority : PublicCorpusCreatesReuseAuthority → ⊥
publicCorpusDoesNotCreateReuseAuthority ()

corpusDescriptionDoesNotCreateEventReceipt : CorpusDescriptionCreatesEventReceipt → ⊥
corpusDescriptionDoesNotCreateEventReceipt ()

transcriptAvailabilityIsNotAcquisition : TranscriptAvailabilityCreatesTranscriptAcquisition → ⊥
transcriptAvailabilityIsNotAcquisition ()

mediaAvailabilityIsNotAcquisition : MediaAvailabilityCreatesMediaAcquisition → ⊥
mediaAvailabilityIsNotAcquisition ()

corpusTermsNeedExactEventBinding : CorpusLevelTermsAutomaticallyBindEveryEvent → ⊥
corpusTermsNeedExactEventBinding ()

candidateDoesNotCreateLinguisticFinding : CorpusCandidateCreatesLinguisticFinding → ⊥
candidateDoesNotCreateLinguisticFinding ()

record OpenCorpusAcquisitionBoundary : Set where
  constructor open-corpus-acquisition-boundary
  field
    publicDiscoverySeparatedFromAcquisition : Bool
    corpusAvailabilitySeparatedFromRights : Bool
    corpusMetadataSeparatedFromEventEvidence : Bool
    exactSnapshotRequired : Bool
    exactEventRequired : Bool
    rawMediaRedistributionAssumed : Bool
open OpenCorpusAcquisitionBoundary public

canonicalOpenCorpusAcquisitionBoundary : OpenCorpusAcquisitionBoundary
canonicalOpenCorpusAcquisitionBoundary =
  open-corpus-acquisition-boundary true true true true true false
