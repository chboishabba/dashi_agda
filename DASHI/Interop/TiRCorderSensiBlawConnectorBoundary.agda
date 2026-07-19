module DASHI.Interop.TiRCorderSensiBlawConnectorBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- TiRCorder -> SensiBlaw connector boundary.
--
-- TiRCorder owns capture, file handling, transcription, diarisation,
-- segmentation, timing, and source hashes.  SensiBlaw owns tokenisation, NLP,
-- concepts, actor resolution, events, harms, claims, ontology, rule atoms,
-- graph construction, policy evaluation, and Streamline materialisation.

data SegmentKind : Set where
  speechSegment : SegmentKind
  silenceSegment : SegmentKind
  noiseSegment : SegmentKind
  overlapSegment : SegmentKind

data HashKind : Set where
  sha256Hash : HashKind

record WordTiming : Set where
  constructor wordTiming
  field
    wordText : String
    startMillis : Nat
    endMillis : Nat
    confidencePermille : Nat

record SentenceBoundaryHint : Set where
  constructor sentenceBoundaryHint
  field
    charStart : Nat
    charEnd : Nat

record CaptureSegment : Set where
  constructor captureSegment
  field
    segmentStartMillis : Nat
    segmentEndMillis : Nat
    segmentKind : SegmentKind

record UtteranceFrame : Set where
  constructor utteranceFrame
  field
    utteranceId : String
    startTimestamp : String
    endTimestamp : String
    speakerLabel : String
    speakerConfidencePermille : Nat
    transcriptText : String
    words : List WordTiming
    sentenceBoundaryHints : List SentenceBoundaryHint
    silenceBeforeMillis : Nat
    silenceAfterMillis : Nat
    energyPermille : Nat

record CaptureProvenance : Set where
  constructor captureProvenance
  field
    deviceId : String
    sessionId : String
    sourcePath : String
    audioHashKind : HashKind
    audioHash : String
    transcriptHashKind : HashKind
    transcriptHash : String
    captureStartedAt : String
    captureEndedAt : String

record TiRCSessionPacket : Set where
  constructor tiRCSessionPacket
  field
    provenance : CaptureProvenance
    utterances : List UtteranceFrame
    segments : List CaptureSegment
    rawPayloadReference : String

record NormalizedTiRCBatch : Set where
  constructor normalizedTiRCBatch
  field
    connectorName : String
    batchId : String
    emittedAt : String
    cursor : String
    nextCursor : String
    sessions : List TiRCSessionPacket

record TiRCorderAuthorityBits : Set where
  field
    ownsCapture : Bool
    ownsCaptureIsTrue : ownsCapture ≡ true
    ownsFileHandling : Bool
    ownsFileHandlingIsTrue : ownsFileHandling ≡ true
    ownsTranscription : Bool
    ownsTranscriptionIsTrue : ownsTranscription ≡ true
    ownsDiarisation : Bool
    ownsDiarisationIsTrue : ownsDiarisation ≡ true
    ownsSegmentation : Bool
    ownsSegmentationIsTrue : ownsSegmentation ≡ true
    ownsSourceProvenance : Bool
    ownsSourceProvenanceIsTrue : ownsSourceProvenance ≡ true
    ownsNLP : Bool
    ownsNLPIsFalse : ownsNLP ≡ false
    ownsCanonicalActorResolution : Bool
    ownsCanonicalActorResolutionIsFalse : ownsCanonicalActorResolution ≡ false
    ownsLegalOntology : Bool
    ownsLegalOntologyIsFalse : ownsLegalOntology ≡ false
    ownsRuleLogic : Bool
    ownsRuleLogicIsFalse : ownsRuleLogic ≡ false
    ownsGraphProjection : Bool
    ownsGraphProjectionIsFalse : ownsGraphProjection ≡ false

record SensiBlawAuthorityBits : Set where
  field
    ownsTextSubstrate : Bool
    ownsTextSubstrateIsTrue : ownsTextSubstrate ≡ true
    ownsNLP : Bool
    ownsNLPIsTrue : ownsNLP ≡ true
    ownsConceptMapping : Bool
    ownsConceptMappingIsTrue : ownsConceptMapping ≡ true
    ownsCanonicalActorResolution : Bool
    ownsCanonicalActorResolutionIsTrue : ownsCanonicalActorResolution ≡ true
    ownsEventConstruction : Bool
    ownsEventConstructionIsTrue : ownsEventConstruction ≡ true
    ownsClaimsHarmsWrongs : Bool
    ownsClaimsHarmsWrongsIsTrue : ownsClaimsHarmsWrongs ≡ true
    ownsRuleAtoms : Bool
    ownsRuleAtomsIsTrue : ownsRuleAtoms ≡ true
    ownsGraphProjection : Bool
    ownsGraphProjectionIsTrue : ownsGraphProjection ≡ true
    ownsPolicyEvaluation : Bool
    ownsPolicyEvaluationIsTrue : ownsPolicyEvaluation ≡ true
    ownsStreamlineMaterialisation : Bool
    ownsStreamlineMaterialisationIsTrue : ownsStreamlineMaterialisation ≡ true

open TiRCorderAuthorityBits public
open SensiBlawAuthorityBits public

canonicalTiRCorderAuthorityBits : TiRCorderAuthorityBits
canonicalTiRCorderAuthorityBits =
  record
    { ownsCapture = true
    ; ownsCaptureIsTrue = refl
    ; ownsFileHandling = true
    ; ownsFileHandlingIsTrue = refl
    ; ownsTranscription = true
    ; ownsTranscriptionIsTrue = refl
    ; ownsDiarisation = true
    ; ownsDiarisationIsTrue = refl
    ; ownsSegmentation = true
    ; ownsSegmentationIsTrue = refl
    ; ownsSourceProvenance = true
    ; ownsSourceProvenanceIsTrue = refl
    ; ownsNLP = false
    ; ownsNLPIsFalse = refl
    ; ownsCanonicalActorResolution = false
    ; ownsCanonicalActorResolutionIsFalse = refl
    ; ownsLegalOntology = false
    ; ownsLegalOntologyIsFalse = refl
    ; ownsRuleLogic = false
    ; ownsRuleLogicIsFalse = refl
    ; ownsGraphProjection = false
    ; ownsGraphProjectionIsFalse = refl
    }

canonicalSensiBlawAuthorityBits : SensiBlawAuthorityBits
canonicalSensiBlawAuthorityBits =
  record
    { ownsTextSubstrate = true
    ; ownsTextSubstrateIsTrue = refl
    ; ownsNLP = true
    ; ownsNLPIsTrue = refl
    ; ownsConceptMapping = true
    ; ownsConceptMappingIsTrue = refl
    ; ownsCanonicalActorResolution = true
    ; ownsCanonicalActorResolutionIsTrue = refl
    ; ownsEventConstruction = true
    ; ownsEventConstructionIsTrue = refl
    ; ownsClaimsHarmsWrongs = true
    ; ownsClaimsHarmsWrongsIsTrue = refl
    ; ownsRuleAtoms = true
    ; ownsRuleAtomsIsTrue = refl
    ; ownsGraphProjection = true
    ; ownsGraphProjectionIsTrue = refl
    ; ownsPolicyEvaluation = true
    ; ownsPolicyEvaluationIsTrue = refl
    ; ownsStreamlineMaterialisation = true
    ; ownsStreamlineMaterialisationIsTrue = refl
    }

record TiRCorderSensiBlawConnectorBoundary : Set where
  field
    sampleBatch : NormalizedTiRCBatch
    tiRCorderAuthority : TiRCorderAuthorityBits
    sensiBlawAuthority : SensiBlawAuthorityBits
    packetContainsGraphNodes : Bool
    packetContainsGraphNodesIsFalse : packetContainsGraphNodes ≡ false
    packetContainsLegalEdges : Bool
    packetContainsLegalEdgesIsFalse : packetContainsLegalEdges ≡ false
    packetContainsCanonicalActors : Bool
    packetContainsCanonicalActorsIsFalse : packetContainsCanonicalActors ≡ false
    packetIsReplayable : Bool
    packetIsReplayableIsTrue : packetIsReplayable ≡ true
    packetIsTamperEvident : Bool
    packetIsTamperEvidentIsTrue : packetIsTamperEvident ≡ true
    batchIngestionIsAtomic : Bool
    batchIngestionIsAtomicIsTrue : batchIngestionIsAtomic ≡ true
    notes : List String

open TiRCorderSensiBlawConnectorBoundary public

canonicalTiRCorderSensiBlawConnectorBoundary :
  TiRCorderSensiBlawConnectorBoundary
canonicalTiRCorderSensiBlawConnectorBoundary =
  record
    { sampleBatch =
        normalizedTiRCBatch
          "tircorder"
          "batch-0"
          "1970-01-01T00:00:00Z"
          ""
          ""
          []
    ; tiRCorderAuthority = canonicalTiRCorderAuthorityBits
    ; sensiBlawAuthority = canonicalSensiBlawAuthorityBits
    ; packetContainsGraphNodes = false
    ; packetContainsGraphNodesIsFalse = refl
    ; packetContainsLegalEdges = false
    ; packetContainsLegalEdgesIsFalse = refl
    ; packetContainsCanonicalActors = false
    ; packetContainsCanonicalActorsIsFalse = refl
    ; packetIsReplayable = true
    ; packetIsReplayableIsTrue = refl
    ; packetIsTamperEvident = true
    ; packetIsTamperEvidentIsTrue = refl
    ; batchIngestionIsAtomic = true
    ; batchIngestionIsAtomicIsTrue = refl
    ; notes =
        "TiRCorder emits capture facts and transcript/file provenance, not interpreted legal or semantic structure."
      ∷ "Speaker labels remain aliases; SensiBlaw resolves canonical actors after ingestion."
      ∷ "Sentence boundaries are hints over transcript text; SensiBlaw owns the canonical text substrate and NLP pass."
      ∷ "Streamline is materialised downstream from SensiBlaw events, finance links, provenance, and cached joins."
      ∷ []
    }
