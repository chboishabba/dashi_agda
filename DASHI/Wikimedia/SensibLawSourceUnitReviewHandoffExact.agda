module DASHI.Wikimedia.SensibLawSourceUnitReviewHandoffExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.SourceProvenanceExact as Source

------------------------------------------------------------------------
-- GENERIC SENSIBLAW SOURCE-UNIT / REVIEW-PACKET ABI
--
-- Runtime donors pinned on SensibLaw/main d25cddf...:
--   schemas/sl.source_unit.v1.schema.yaml
--   docs/planning/wikidata_review_packet_contract_20260401.md
--   src/ontology/wikidata.py
------------------------------------------------------------------------

data OptionalText : Set where
  absentText : OptionalText
  presentText : String → OptionalText

data RevisionId : Set where
  textualRevisionId : String → RevisionId
  numericRevisionId : Nat → RevisionId

data RetrievalMethod : Set where
  pdfSnapshot htmlSnapshot wikiRevision csvSnapshot chatCapture otherRetrieval
  : RetrievalMethod

data SourceType : Set where
  pdfSource htmlSource wikiSource csvSource chatSource textSource otherSource
  : SourceType

data ContentFormat : Set where
  textFormat htmlFormat markdownFormat csvFormat otherFormat
  : ContentFormat

record SourceRevision : Set where
  constructor source-revision
  field
    revisionId : RevisionId
    revisionTimestamp : String
    retrievalMethod : RetrievalMethod
open SourceRevision public

record SourceOrigin : Set where
  constructor source-origin
  field
    sourceType : SourceType
    sourceUrl : OptionalText
    title : OptionalText
open SourceOrigin public

record SourceAnchor : Set where
  constructor source-anchor
  field
    anchorId : String
    startOffset : Nat
    endOffset : Nat
    anchorLabel : OptionalText
open SourceAnchor public

record SourceContent : Set where
  constructor source-content
  field
    contentFormat : ContentFormat
    sourceText : String
open SourceContent public

record SensibLawSourceUnit : Set where
  constructor sensiblaw-source-unit
  field
    sourceId : String
    entityQid : Id.ItemId
    sourceUnitId : String
    revision : SourceRevision
    origin : SourceOrigin
    content : SourceContent
    anchors : List SourceAnchor
    sourceMetadataReference : String
    sourceReceipt : Source.SourceReceipt
    contractReference : String
open SensibLawSourceUnit public

------------------------------------------------------------------------
-- Reviewer packet / execution separation.
------------------------------------------------------------------------

data ReviewRoute : Set where
  fullAuto
  splitAuto
  repairPlusMigrateReview
  reviewOnlyTypedHold
  manualReconstruction
  : ReviewRoute

data MigrationDisposition : Set where
  safeEquivalent
  safeWithReferenceTransfer
  qualifierDrift
  referenceDrift
  ambiguousSemantics
  nonEquivalent
  needsHumanReview
  abstain
  splitRequired
  : MigrationDisposition

record SplitReviewContext : Set where
  constructor split-review-context
  field
    splitPlanId : String
    sourceSlotId : String
    sourceCandidateReferences : List String
    splitAxes : List String
    route : ReviewRoute
    disposition : MigrationDisposition
    propagationExpectation : String
open SplitReviewContext public

record ParsedPageSignals : Set where
  constructor parsed-page-signals
  field
    queryLinks : List String
    citedOutboundLinks : List String
    unresolvedQuestions : List String
    expectedQualifierProperties : List Id.PropertyId
    expectedReferenceProperties : List Id.PropertyId
    parseReference : String
open ParsedPageSignals public

record FollowReceipt : Set where
  constructor follow-receipt
  field
    followedReference : String
    followReason : String
    extractedEvidenceReference : String
    remainingUncertainty : String
open FollowReceipt public

record ReviewerView : Set where
  constructor reviewer-view
  field
    decisionFocus : List String
    uncertaintyFlags : List String
    recommendedNextStep : String
open ReviewerView public

record SensibLawReviewPacket : Set where
  constructor sensiblaw-review-packet
  field
    packetId : String
    sourceUnit : SensibLawSourceUnit
    splitContext : SplitReviewContext
    parsedSignals : ParsedPageSignals
    followReceipts : List FollowReceipt
    reviewerView : ReviewerView
    splitPlanRemainsExecutionBaseline : Bool
    splitPlanRemainsExecutionBaselineIsTrue : splitPlanRemainsExecutionBaseline ≡ true
    unresolvedUncertaintyVisible : Bool
    unresolvedUncertaintyVisibleIsTrue : unresolvedUncertaintyVisible ≡ true
    packetReference : String
open SensibLawReviewPacket public

------------------------------------------------------------------------
-- SLR reuse boundary.
------------------------------------------------------------------------

data RuntimeConsumer : Set where
  historicalSensibLawPython
  slrRustRuntime
  : RuntimeConsumer

record RuntimeHandoffReceipt : Set where
  constructor runtime-handoff-receipt
  field
    consumer : RuntimeConsumer
    sourceUnitReference : String
    packetReference : String
    consumerContractReference : String
    revisionIdentityPreserved : Bool
    revisionIdentityPreservedIsTrue : revisionIdentityPreserved ≡ true
    sourceAnchorsPreserved : Bool
    sourceAnchorsPreservedIsTrue : sourceAnchorsPreserved ≡ true
    runtimeOwnsSourceAuthority : Bool
    runtimeOwnsSourceAuthorityIsFalse : runtimeOwnsSourceAuthority ≡ false
    runtimeOwnsSemanticPromotion : Bool
    runtimeOwnsSemanticPromotionIsFalse : runtimeOwnsSemanticPromotion ≡ false
open RuntimeHandoffReceipt public

data ReviewPacketCreatesAuthority : Set where
data ShallowParseIsFullSemanticDecomposition : Set where
data FollowReceiptMeansGroundedTruth : Set where
data RuntimeConsumptionMeansPromotion : Set where
data SplitRequiredMeansUnsafeSource : Set where

reviewPacketDoesNotCreateAuthority : ReviewPacketCreatesAuthority → ⊥
reviewPacketDoesNotCreateAuthority ()
shallowParseDoesNotBecomeFullSemantics : ShallowParseIsFullSemanticDecomposition → ⊥
shallowParseDoesNotBecomeFullSemantics ()
followReceiptDoesNotMeanGroundedTruth : FollowReceiptMeansGroundedTruth → ⊥
followReceiptDoesNotMeanGroundedTruth ()
runtimeConsumptionDoesNotMeanPromotion : RuntimeConsumptionMeansPromotion → ⊥
runtimeConsumptionDoesNotMeanPromotion ()
splitRequiredDoesNotMeanSourceUnsafe : SplitRequiredMeansUnsafeSource → ⊥
splitRequiredDoesNotMeanSourceUnsafe ()

record SensibLawHandoffBoundary : Set where
  constructor sensiblaw-handoff-boundary
  field
    sourceUnitsRevisionLocked : Bool
    sourceUnitSchemaPreservesNullableOriginFields : Bool
    sourceUnitSchemaPreservesStringOrIntegerRevisionIds : Bool
    reviewPacketsPreserveSplitBaseline : Bool
    reviewPacketsTransferAuthority : Bool
    parserOutputOwnsCanonicalSemantics : Bool
    slrConsumptionOwnsPromotion : Bool

canonicalSensibLawHandoffBoundary : SensibLawHandoffBoundary
canonicalSensibLawHandoffBoundary =
  sensiblaw-handoff-boundary true true true true false false false
