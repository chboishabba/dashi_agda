module DASHI.Interop.TiRCorderCaptureIntakeTranscriptionAdaptersExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.TiRCorderSensiBlawConnectorBoundary as Boundary

------------------------------------------------------------------------
-- Capture / intake / transcription adapters.
--
-- This module is a thin producer for the existing TiRCorder packet surface.
-- It does not define downstream NLP, legal, actor, graph, or policy semantics.
------------------------------------------------------------------------

record CaptureInput : Set where
  constructor captureInput
  field
    deviceId : String
    sessionId : String
    sourcePath : String
    audioHash : String
    captureStartedAt : String
    captureEndedAt : String

open CaptureInput public

record TranscriptInput : Set where
  constructor transcriptInput
  field
    utteranceId : String
    startTimestamp : String
    endTimestamp : String
    speakerLabel : String
    speakerConfidencePermille : Nat
    transcriptText : String
    words : List Boundary.WordTiming
    sentenceBoundaryHints : List Boundary.SentenceBoundaryHint
    silenceBeforeMillis : Nat
    silenceAfterMillis : Nat
    energyPermille : Nat

open TranscriptInput public

record IntakeInput : Set where
  constructor intakeInput
  field
    capture : CaptureInput
    transcriptHash : String
    transcripts : List TranscriptInput
    segments : List Boundary.CaptureSegment
    rawPayloadReference : String

open IntakeInput public

captureAdapter : CaptureInput → String → Boundary.CaptureProvenance
captureAdapter source transcriptHash =
  Boundary.captureProvenance
    (deviceId source)
    (sessionId source)
    (sourcePath source)
    Boundary.sha256Hash
    (audioHash source)
    Boundary.sha256Hash
    transcriptHash
    (captureStartedAt source)
    (captureEndedAt source)

transcriptionAdapter : TranscriptInput → Boundary.UtteranceFrame
transcriptionAdapter transcript =
  Boundary.utteranceFrame
    (utteranceId transcript)
    (startTimestamp transcript)
    (endTimestamp transcript)
    (speakerLabel transcript)
    (speakerConfidencePermille transcript)
    (transcriptText transcript)
    (words transcript)
    (sentenceBoundaryHints transcript)
    (silenceBeforeMillis transcript)
    (silenceAfterMillis transcript)
    (energyPermille transcript)

mapTranscripts : List TranscriptInput → List Boundary.UtteranceFrame
mapTranscripts [] = []
mapTranscripts (transcript ∷ rest) =
  transcriptionAdapter transcript ∷ mapTranscripts rest

intakeAdapter : IntakeInput → Boundary.TiRCSessionPacket
intakeAdapter source =
  Boundary.tiRCSessionPacket
    (captureAdapter (capture source) (transcriptHash source))
    (mapTranscripts (transcripts source))
    (segments source)
    (rawPayloadReference source)

record BatchInput : Set where
  constructor batchInput
  field
    batchId : String
    emittedAt : String
    cursor : String
    nextCursor : String
    sessions : List IntakeInput

open BatchInput public

mapSessions : List IntakeInput → List Boundary.TiRCSessionPacket
mapSessions [] = []
mapSessions (session ∷ rest) =
  intakeAdapter session ∷ mapSessions rest

batchAdapter : BatchInput → Boundary.NormalizedTiRCBatch
batchAdapter source =
  Boundary.normalizedTiRCBatch
    "tircorder"
    (batchId source)
    (emittedAt source)
    (cursor source)
    (nextCursor source)
    (mapSessions (sessions source))

------------------------------------------------------------------------
-- Exact preservation laws.
------------------------------------------------------------------------

captureDevicePreserved :
  ∀ source transcriptHash →
  Boundary.CaptureProvenance.deviceId
    (captureAdapter source transcriptHash)
  ≡ deviceId source
captureDevicePreserved source transcriptHash = refl

captureSessionPreserved :
  ∀ source transcriptHash →
  Boundary.CaptureProvenance.sessionId
    (captureAdapter source transcriptHash)
  ≡ sessionId source
captureSessionPreserved source transcriptHash = refl

captureAudioHashPreserved :
  ∀ source transcriptHash →
  Boundary.CaptureProvenance.audioHash
    (captureAdapter source transcriptHash)
  ≡ audioHash source
captureAudioHashPreserved source transcriptHash = refl

captureTranscriptHashPreserved :
  ∀ source transcriptHash →
  Boundary.CaptureProvenance.transcriptHash
    (captureAdapter source transcriptHash)
  ≡ transcriptHash
captureTranscriptHashPreserved source transcriptHash = refl

transcriptTextPreserved :
  ∀ source →
  Boundary.UtteranceFrame.transcriptText
    (transcriptionAdapter source)
  ≡ transcriptText source
transcriptTextPreserved source = refl

transcriptSpeakerLabelPreserved :
  ∀ source →
  Boundary.UtteranceFrame.speakerLabel
    (transcriptionAdapter source)
  ≡ speakerLabel source
transcriptSpeakerLabelPreserved source = refl

transcriptWordsPreserved :
  ∀ source →
  Boundary.UtteranceFrame.words
    (transcriptionAdapter source)
  ≡ words source
transcriptWordsPreserved source = refl

intakeRawPayloadReferencePreserved :
  ∀ source →
  Boundary.TiRCSessionPacket.rawPayloadReference
    (intakeAdapter source)
  ≡ rawPayloadReference source
intakeRawPayloadReferencePreserved source = refl

intakeSegmentsPreserved :
  ∀ source →
  Boundary.TiRCSessionPacket.segments
    (intakeAdapter source)
  ≡ segments source
intakeSegmentsPreserved source = refl

batchIdentityPreserved :
  ∀ source →
  Boundary.NormalizedTiRCBatch.batchId
    (batchAdapter source)
  ≡ batchId source
batchIdentityPreserved source = refl

batchCursorPreserved :
  ∀ source →
  Boundary.NormalizedTiRCBatch.cursor
    (batchAdapter source)
  ≡ cursor source
batchCursorPreserved source = refl

batchNextCursorPreserved :
  ∀ source →
  Boundary.NormalizedTiRCBatch.nextCursor
    (batchAdapter source)
  ≡ nextCursor source
batchNextCursorPreserved source = refl

------------------------------------------------------------------------
-- Consumer and authority firewalls.
------------------------------------------------------------------------

data CaptureAdapterCreatesNLP : Set where
data IntakeAdapterCreatesCanonicalActor : Set where
data TranscriptionAdapterCreatesLegalOntology : Set where
data TranscriptTextCreatesGraphProjection : Set where

captureAdapterDoesNotCreateNLP : CaptureAdapterCreatesNLP → ⊥
captureAdapterDoesNotCreateNLP ()

intakeAdapterDoesNotCreateCanonicalActor :
  IntakeAdapterCreatesCanonicalActor → ⊥
intakeAdapterDoesNotCreateCanonicalActor ()

transcriptionAdapterDoesNotCreateLegalOntology :
  TranscriptionAdapterCreatesLegalOntology → ⊥
transcriptionAdapterDoesNotCreateLegalOntology ()

transcriptTextDoesNotCreateGraphProjection :
  TranscriptTextCreatesGraphProjection → ⊥
transcriptTextDoesNotCreateGraphProjection ()

record CaptureIntakeTranscriptionAdapterBoundary : Set where
  constructor captureIntakeTranscriptionAdapterBoundary
  field
    captureIsOwnedByTiRCorder : Bool
    captureIsOwnedByTiRCorderIsTrue :
      captureIsOwnedByTiRCorder ≡ true

    transcriptionIsOwnedByTiRCorder : Bool
    transcriptionIsOwnedByTiRCorderIsTrue :
      transcriptionIsOwnedByTiRCorder ≡ true

    adapterCreatesNLP : Bool
    adapterCreatesNLPIsFalse :
      adapterCreatesNLP ≡ false

    adapterCreatesCanonicalActors : Bool
    adapterCreatesCanonicalActorsIsFalse :
      adapterCreatesCanonicalActors ≡ false

    adapterCreatesLegalOntology : Bool
    adapterCreatesLegalOntologyIsFalse :
      adapterCreatesLegalOntology ≡ false

    adapterCreatesGraphProjection : Bool
    adapterCreatesGraphProjectionIsFalse :
      adapterCreatesGraphProjection ≡ false

open CaptureIntakeTranscriptionAdapterBoundary public

canonicalCaptureIntakeTranscriptionAdapterBoundary :
  CaptureIntakeTranscriptionAdapterBoundary
canonicalCaptureIntakeTranscriptionAdapterBoundary =
  captureIntakeTranscriptionAdapterBoundary
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
