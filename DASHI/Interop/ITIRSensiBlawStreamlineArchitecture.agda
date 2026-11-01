module DASHI.Interop.ITIRSensiBlawStreamlineArchitecture where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Interop.ITIRActorIdentitySpine as ActorSpine
import DASHI.Interop.PolisITIRDeliberationBoundary as Polis
import DASHI.Interop.TiRCorderSensiBlawConnectorBoundary as TiRCSL

------------------------------------------------------------------------
-- Master candidate-only architecture for ITIR / TiRCorder / SensiBlaw /
-- Streamline and the Pol.is deliberation sidecar.
--
-- This is a typed responsibility and provenance boundary, not a claim that
-- Agda proves the truth of extracted narratives, legal classifications,
-- financial inferences, community preferences, or real-world outcomes.

data PipelineStage : Set where
  captureStage : PipelineStage
  fileAndTranscriptStage : PipelineStage
  textSubstrateStage : PipelineStage
  actorEventStage : PipelineStage
  claimHarmEvidenceStage : PipelineStage
  ontologyRuleStage : PipelineStage
  financeReconciliationStage : PipelineStage
  graphProjectionStage : PipelineStage
  persistedViewStage : PipelineStage
  streamlineStage : PipelineStage
  correctionReceiptStage : PipelineStage
  deliberationSidecarStage : PipelineStage

data DataAuthorityKind : Set where
  captureAuthority : DataAuthorityKind
  substrateAuthority : DataAuthorityKind
  semanticAuthority : DataAuthorityKind
  legalLogicAuthority : DataAuthorityKind
  financeInferenceAuthority : DataAuthorityKind
  graphProjectionAuthority : DataAuthorityKind
  visualProjectionAuthority : DataAuthorityKind
  humanCorrectionAuthority : DataAuthorityKind
  deliberationAuthority : DataAuthorityKind

data ExternalOntologyProvider : Set where
  wikidataProvider : ExternalOntologyProvider
  dbpediaProvider : ExternalOntologyProvider
  yagoProvider : ExternalOntologyProvider
  wordnetProvider : ExternalOntologyProvider
  schemaOrgProvider : ExternalOntologyProvider
  otherOntologyProvider : ExternalOntologyProvider

record ConceptExternalReference : Set where
  constructor conceptExternalReference
  field
    internalConceptId : Nat
    provider : ExternalOntologyProvider
    externalIdentifier : String
    cachedLabel : String
    confidencePermille : Nat
    humanConfirmed : Bool

record FinancePosting : Set where
  constructor financePosting
  field
    postingId : Nat
    accountId : Nat
    postedAt : String
    signedMinorUnits : Nat
    currencyCode : String
    rawPayloadHash : String

record FinanceTransferInference : Set where
  constructor financeTransferInference
  field
    transferId : Nat
    sourcePostingId : Nat
    destinationPostingId : Nat
    inferenceRule : String
    confidencePermille : Nat

record PersistedStreamlineRow : Set where
  constructor persistedStreamlineRow
  field
    rowId : Nat
    timelineTimestamp : String
    laneId : String
    proportionalWidth : Nat
    transferReference : Nat
    eventReference : Nat
    sentenceReference : Nat
    cacheGeneration : Nat

record CorrectionLedgerEntry : Set where
  constructor correctionLedgerEntry
  field
    correctionId : Nat
    targetKind : String
    targetId : Nat
    previousVersion : Nat
    replacementVersion : Nat
    correctionReason : String
    correctionHash : String

record ReceiptPack : Set where
  constructor receiptPack
  field
    packId : String
    canonicalPayloadHash : String
    signerKeyId : String
    signatureReference : String
    includedObjectIds : List Nat

record StageOwnershipRow : Set where
  constructor stageOwnershipRow
  field
    stage : PipelineStage
    authority : DataAuthorityKind
    ownerLabel : String
    inputLabel : String
    outputLabel : String

record ArchitectureAuthorityBits : Set where
  field
    relationalTablesAreCanonical : Bool
    relationalTablesAreCanonicalIsTrue :
      relationalTablesAreCanonical ≡ true
    graphIsDerivedProjection : Bool
    graphIsDerivedProjectionIsTrue : graphIsDerivedProjection ≡ true
    streamlineUsesPersistedCacheTables : Bool
    streamlineUsesPersistedCacheTablesIsTrue :
      streamlineUsesPersistedCacheTables ≡ true
    rawFinancePostingsAreImmutable : Bool
    rawFinancePostingsAreImmutableIsTrue : rawFinancePostingsAreImmutable ≡ true
    transferPairsAreInferredSeparately : Bool
    transferPairsAreInferredSeparatelyIsTrue :
      transferPairsAreInferredSeparately ≡ true
    externalOntologiesAreAdvisory : Bool
    externalOntologiesAreAdvisoryIsTrue : externalOntologiesAreAdvisory ≡ true
    externalOntologiesAreNormativeAuthority : Bool
    externalOntologiesAreNormativeAuthorityIsFalse :
      externalOntologiesAreNormativeAuthority ≡ false
    correctionsAreAppendOnly : Bool
    correctionsAreAppendOnlyIsTrue : correctionsAreAppendOnly ≡ true
    receiptsAreTamperEvident : Bool
    receiptsAreTamperEvidentIsTrue : receiptsAreTamperEvident ≡ true
    modelOutputIsNotEvidenceByItself : Bool
    modelOutputIsNotEvidenceByItselfIsTrue :
      modelOutputIsNotEvidenceByItself ≡ true
    visualisationIsNotCausalProof : Bool
    visualisationIsNotCausalProofIsTrue :
      visualisationIsNotCausalProof ≡ true
    legalClassificationIsNotLegalAuthority : Bool
    legalClassificationIsNotLegalAuthorityIsTrue :
      legalClassificationIsNotLegalAuthority ≡ true

open ArchitectureAuthorityBits public

canonicalArchitectureAuthorityBits : ArchitectureAuthorityBits
canonicalArchitectureAuthorityBits =
  record
    { relationalTablesAreCanonical = true
    ; relationalTablesAreCanonicalIsTrue = refl
    ; graphIsDerivedProjection = true
    ; graphIsDerivedProjectionIsTrue = refl
    ; streamlineUsesPersistedCacheTables = true
    ; streamlineUsesPersistedCacheTablesIsTrue = refl
    ; rawFinancePostingsAreImmutable = true
    ; rawFinancePostingsAreImmutableIsTrue = refl
    ; transferPairsAreInferredSeparately = true
    ; transferPairsAreInferredSeparatelyIsTrue = refl
    ; externalOntologiesAreAdvisory = true
    ; externalOntologiesAreAdvisoryIsTrue = refl
    ; externalOntologiesAreNormativeAuthority = false
    ; externalOntologiesAreNormativeAuthorityIsFalse = refl
    ; correctionsAreAppendOnly = true
    ; correctionsAreAppendOnlyIsTrue = refl
    ; receiptsAreTamperEvident = true
    ; receiptsAreTamperEvidentIsTrue = refl
    ; modelOutputIsNotEvidenceByItself = true
    ; modelOutputIsNotEvidenceByItselfIsTrue = refl
    ; visualisationIsNotCausalProof = true
    ; visualisationIsNotCausalProofIsTrue = refl
    ; legalClassificationIsNotLegalAuthority = true
    ; legalClassificationIsNotLegalAuthorityIsTrue = refl
    }

canonicalStageOwnershipRows : List StageOwnershipRow
canonicalStageOwnershipRows =
    stageOwnershipRow captureStage captureAuthority "TiRCorder" "microphone/audio" "source recording"
  ∷ stageOwnershipRow fileAndTranscriptStage captureAuthority "TiRCorder" "source recording" "transcript, diarisation, timings, hashes"
  ∷ stageOwnershipRow textSubstrateStage substrateAuthority "SensiBlaw" "transcript/documents" "documents, sentences, tokens, phrases"
  ∷ stageOwnershipRow actorEventStage semanticAuthority "SensiBlaw" "speaker aliases and source records" "canonical actors and polymorphic events"
  ∷ stageOwnershipRow claimHarmEvidenceStage semanticAuthority "SensiBlaw plus human review" "events and sentences" "versioned claims, harms, evidence links"
  ∷ stageOwnershipRow ontologyRuleStage legalLogicAuthority "SensiBlaw" "provisions and semantic candidates" "wrong elements, rule atoms, conditions, exceptions"
  ∷ stageOwnershipRow financeReconciliationStage financeInferenceAuthority "SensiBlaw" "immutable account postings" "paired transfers and confidence receipts"
  ∷ stageOwnershipRow graphProjectionStage graphProjectionAuthority "SensiBlaw" "canonical relational rows" "typed temporal graph projection"
  ∷ stageOwnershipRow persistedViewStage visualProjectionAuthority "SensiBlaw" "joined canonical rows" "generation-stamped cache tables"
  ∷ stageOwnershipRow streamlineStage visualProjectionAuthority "Streamline" "persisted cache rows" "interactive ribbons, siphons, events, provenance"
  ∷ stageOwnershipRow correctionReceiptStage humanCorrectionAuthority "ITIR/SensiBlaw" "reviewed rows and exports" "append-only corrections and signed receipt packs"
  ∷ stageOwnershipRow deliberationSidecarStage deliberationAuthority "Pol.is sidecar" "atomic statements and votes" "clusters and bridge statistics"
  ∷ []

record ITIRSensiBlawStreamlineArchitecture : Set where
  field
    actorIdentitySpine : ActorSpine.ITIRActorIdentitySpine
    tiRCorderSensiBlawBoundary : TiRCSL.TiRCorderSensiBlawConnectorBoundary
    polisDeliberationBoundary : Polis.PolisITIRDeliberationBoundary
    stageOwnershipRows : List StageOwnershipRow
    externalConceptReferences : List ConceptExternalReference
    financePostings : List FinancePosting
    transferInferences : List FinanceTransferInference
    persistedStreamlineRows : List PersistedStreamlineRow
    corrections : List CorrectionLedgerEntry
    receiptPacks : List ReceiptPack
    authorityBits : ArchitectureAuthorityBits
    notes : List String

open ITIRSensiBlawStreamlineArchitecture public

canonicalITIRSensiBlawStreamlineArchitecture :
  ITIRSensiBlawStreamlineArchitecture
canonicalITIRSensiBlawStreamlineArchitecture =
  record
    { actorIdentitySpine = ActorSpine.canonicalITIRActorIdentitySpine
    ; tiRCorderSensiBlawBoundary =
        TiRCSL.canonicalTiRCorderSensiBlawConnectorBoundary
    ; polisDeliberationBoundary =
        Polis.canonicalPolisITIRDeliberationBoundary
    ; stageOwnershipRows = canonicalStageOwnershipRows
    ; externalConceptReferences = []
    ; financePostings = []
    ; transferInferences = []
    ; persistedStreamlineRows = []
    ; corrections = []
    ; receiptPacks = []
    ; authorityBits = canonicalArchitectureAuthorityBits
    ; notes =
        "TiRCorder stops at high-fidelity capture/transcription/file provenance; SensiBlaw owns all downstream NLP and logic."
      ∷ "The canonical relational substrate precedes graph projection and persisted Streamline cache rows."
      ∷ "Money flows, narrative events, legal frames, and deliberation outputs remain separately sourced and provenance-bearing."
      ∷ "No visual ribbon, ontology mapping, model score, community cluster, or external ontology reference is promoted to causal, factual, moral, or legal authority."
      ∷ []
    }
