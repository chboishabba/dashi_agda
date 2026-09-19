module DASHI.Education.DigitalESDSLRSourceReviewBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDSearchToSourceAuditAdmissionExact as SearchAudit
import DASHI.Education.DigitalESDSituatedAuditObserverExact as Situated
import DASHI.Interop.SLRWikipediaArticlePNFWorldProducerExact as SLRWorld
import DASHI.Interop.SLRNatClimateSourceUnitPNFBatchExact as SLRBatch
import DASHI.Wikimedia.SensibLawSourceUnitReviewHandoffExact as SensibLaw

------------------------------------------------------------------------
-- DIGITAL-ESD SCREENED FULL-TEXT -> SLR / SENSIBLAW REVIEW BRIDGE
--
-- This is deliberately a second-stage consumer.
--
-- Search/screen lineage must already exist before full text can enter this
-- bridge. SLR/SensibLaw may then decompose the paper into source units,
-- anchored claim candidates, PNF proposals, residuals, and review packets.
-- None of those outputs is a SourceAuditAdmission and none owns paper truth.
--
-- Existing generic donors are reused rather than reconstructed:
--   * GenericTextWorldProducerABI
--   * SourceUnitPNFBatchBoundary
--   * SensibLawHandoffBoundary
--
-- We intentionally do NOT reuse SensibLawSourceUnit itself for arbitrary
-- papers because that concrete carrier currently requires an entity QID.
-- Digital-ESD publication identity remains indexed by AttributedSource and
-- explicit same-object identifier/artifact receipts; no publication QID is
-- invented.
------------------------------------------------------------------------

genericTextProducerBoundary : SLRWorld.GenericTextWorldProducerABI
genericTextProducerBoundary = SLRWorld.canonicalGenericTextWorldProducerABI

sourceUnitBatchBoundary : SLRBatch.SourceUnitPNFBatchBoundary
sourceUnitBatchBoundary = SLRBatch.canonicalSourceUnitPNFBatchBoundary

sensibLawReviewBoundary : SensibLaw.SensibLawHandoffBoundary
sensibLawReviewBoundary = SensibLaw.canonicalSensibLawHandoffBoundary

------------------------------------------------------------------------
-- Same-object publication / full-text carrier.
------------------------------------------------------------------------

data OptionalIdentifier : Set where
  noIdentifier : OptionalIdentifier
  identifier : String → OptionalIdentifier

record FullTextArtifactReceipt (source : Attr.AttributedSource) : Set where
  constructor full-text-artifact-receipt
  field
    includedLineage : SearchAudit.IncludedSourceLineage source
    ericIdentifier : OptionalIdentifier
    doiIdentifier : OptionalIdentifier
    pmidIdentifier : OptionalIdentifier
    fullTextArtifactReference : String
    fullTextArtifactSha256 : String
    retrievalReference : String
    retrievalTimestamp : String
    sameObjectIdentityReference : String
    sameObjectIdentityReviewed : Bool
    sameObjectIdentityReviewedIsTrue : sameObjectIdentityReviewed ≡ true
    titleMatchAlonePaysIdentity : Bool
    titleMatchAlonePaysIdentityIsFalse : titleMatchAlonePaysIdentity ≡ false

open FullTextArtifactReceipt public

------------------------------------------------------------------------
-- SLR / SensibLaw analysis stays candidate-only.
------------------------------------------------------------------------

record SLRSourceUnitAnalysisReceipt (source : Attr.AttributedSource) : Set where
  constructor slr-source-unit-analysis-receipt
  field
    fullText : FullTextArtifactReceipt source
    sourceUnitReference : String
    sourceTextHashReference : String
    revisionOrSnapshotReference : String
    parserReceiptReference : String
    pnfCandidateManifestReference : String
    reviewClaimBundleReference : String
    unresolvedResidualReference : String
    sourceSpanIndexReference : String
    producerABIReference : String
    sourceRoleRetained : Bool
    sourceRoleRetainedIsTrue : sourceRoleRetained ≡ true
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    semanticPromotion : Bool
    semanticPromotionIsFalse : semanticPromotion ≡ false
    runtimeOwnsSourceAuthority : Bool
    runtimeOwnsSourceAuthorityIsFalse : runtimeOwnsSourceAuthority ≡ false

open SLRSourceUnitAnalysisReceipt public

------------------------------------------------------------------------
-- SLR output may propose situated audit observations, but the observation is
-- indexed back to the same AttributedSource and remains review-only.
------------------------------------------------------------------------

record SLRCandidateAuditObservation (source : Attr.AttributedSource) : Set where
  constructor slr-candidate-audit-observation
  field
    analysis : SLRSourceUnitAnalysisReceipt source
    candidateObservation : Situated.SituatedAuditObservation
    candidateObservationSourceIsSame :
      Situated.source candidateObservation ≡ source
    sourceSpanReference : String
    claimCandidateReference : String
    pnfCandidateReference : String
    extractionBasis : String
    candidateForReview : Bool
    candidateForReviewIsTrue : candidateForReview ≡ true
    acceptedAsPaperTruth : Bool
    acceptedAsPaperTruthIsFalse : acceptedAsPaperTruth ≡ false
    createsAuditAdmission : Bool
    createsAuditAdmissionIsFalse : createsAuditAdmission ≡ false

open SLRCandidateAuditObservation public

------------------------------------------------------------------------
-- Review acceptance is an additional coordinate. It may license an extracted
-- observation for use while completing the audit, but still does not discharge
-- the rest of SourceAuditAdmission.
------------------------------------------------------------------------

record SLRObservationReviewReceipt (source : Attr.AttributedSource) : Set where
  constructor slr-observation-review-receipt
  field
    candidate : SLRCandidateAuditObservation source
    reviewerReference : String
    reviewDecisionReference : String
    reviewReason : String
    acceptedForAuditConsideration : Bool
    acceptedForAuditConsiderationIsTrue :
      acceptedForAuditConsideration ≡ true
    acceptedAsSourceTruth : Bool
    acceptedAsSourceTruthIsFalse : acceptedAsSourceTruth ≡ false
    completeAuditCreated : Bool
    completeAuditCreatedIsFalse : completeAuditCreated ≡ false

open SLRObservationReviewReceipt public

record ReviewedSLRAuditObservation (source : Attr.AttributedSource) : Set where
  constructor reviewed-slr-audit-observation
  field
    reviewReceipt : SLRObservationReviewReceipt source
    reviewedObservation : Situated.SituatedAuditObservation
    reviewedObservationSourceIsSame :
      Situated.source reviewedObservation ≡ source
    auditUseReference : String

open ReviewedSLRAuditObservation public

------------------------------------------------------------------------
-- Optional bounded packet for later source-audit completion.
------------------------------------------------------------------------

record SLRSourceReviewPacket (source : Attr.AttributedSource) : Set where
  constructor slr-source-review-packet
  field
    fullText : FullTextArtifactReceipt source
    analysis : SLRSourceUnitAnalysisReceipt source
    candidateObservations : List (SLRCandidateAuditObservation source)
    reviewedObservations : List (ReviewedSLRAuditObservation source)
    unresolvedResidualsReference : String
    tensionComparisonReference : String
    packetReference : String
    sourceAuditStillSeparate : Bool
    sourceAuditStillSeparateIsTrue : sourceAuditStillSeparate ≡ true

open SLRSourceReviewPacket public


------------------------------------------------------------------------
-- Optional final same-source product: SLR sidecar accompanies an already
-- admitted corpus source. The constructor requires CorpusAuditedSource rather
-- than deriving it.
------------------------------------------------------------------------

record SLRAssistedCorpusAuditedSource (source : Attr.AttributedSource) : Set where
  constructor slr-assisted-corpus-audited-source
  field
    corpusSource : SearchAudit.CorpusAuditedSource source
    slrReviewPacket : SLRSourceReviewPacket source
    sidecarReference : String
    slrSidecarCreatesAdmission : Bool
    slrSidecarCreatesAdmissionIsFalse : slrSidecarCreatesAdmission ≡ false

open SLRAssistedCorpusAuditedSource public

mkSLRAssistedCorpusAuditedSource :
  (source : Attr.AttributedSource) →
  SearchAudit.CorpusAuditedSource source →
  SLRSourceReviewPacket source →
  String →
  SLRAssistedCorpusAuditedSource source
mkSLRAssistedCorpusAuditedSource source corpus packet ref =
  slr-assisted-corpus-audited-source corpus packet ref false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MetadataOnlyCandidateEntersSLRSecondStage : Set where
data SLRExtractionCreatesSourceAuditAdmission : Set where
data SLRClaimCandidateCreatesPaperTruth : Set where
data ReviewedSLRObservationCreatesSourceAuditAdmission : Set where
data TitleMatchCreatesSameObjectPaperIdentity : Set where
data SLRRuntimeCreatesCorpusInclusion : Set where
data PNFResidualCreatesEmpiricalFact : Set where
data ReviewPacketRaisesClaimCeiling : Set where
data SLRReviewPacketCreatesCorpusAuditedSource : Set where

metadataOnlyCandidateDoesNotEnterSLRSecondStage :
  MetadataOnlyCandidateEntersSLRSecondStage → ⊥
metadataOnlyCandidateDoesNotEnterSLRSecondStage ()

slrExtractionDoesNotCreateSourceAuditAdmission :
  SLRExtractionCreatesSourceAuditAdmission → ⊥
slrExtractionDoesNotCreateSourceAuditAdmission ()

slrClaimCandidateDoesNotCreatePaperTruth :
  SLRClaimCandidateCreatesPaperTruth → ⊥
slrClaimCandidateDoesNotCreatePaperTruth ()

reviewedSLRObservationDoesNotCreateSourceAuditAdmission :
  ReviewedSLRObservationCreatesSourceAuditAdmission → ⊥
reviewedSLRObservationDoesNotCreateSourceAuditAdmission ()

titleMatchDoesNotCreateSameObjectPaperIdentity :
  TitleMatchCreatesSameObjectPaperIdentity → ⊥
titleMatchDoesNotCreateSameObjectPaperIdentity ()

slrRuntimeDoesNotCreateCorpusInclusion :
  SLRRuntimeCreatesCorpusInclusion → ⊥
slrRuntimeDoesNotCreateCorpusInclusion ()

pnfResidualDoesNotCreateEmpiricalFact :
  PNFResidualCreatesEmpiricalFact → ⊥
pnfResidualDoesNotCreateEmpiricalFact ()

reviewPacketDoesNotRaiseClaimCeiling :
  ReviewPacketRaisesClaimCeiling → ⊥
reviewPacketDoesNotRaiseClaimCeiling ()

slrReviewPacketDoesNotCreateCorpusAuditedSource :
  SLRReviewPacketCreatesCorpusAuditedSource → ⊥
slrReviewPacketDoesNotCreateCorpusAuditedSource ()

------------------------------------------------------------------------
-- Boundary / roadmap reading.
------------------------------------------------------------------------

record DigitalESDSLRBridgeBoundary : Set where
  constructor digital-esd-slr-bridge-boundary
  field
    screenedLineageRequiredBeforeSLR : Bool
    screenedLineageRequiredBeforeSLRIsTrue :
      screenedLineageRequiredBeforeSLR ≡ true
    fullTextHashRequired : Bool
    fullTextHashRequiredIsTrue : fullTextHashRequired ≡ true
    publicationQidRequired : Bool
    publicationQidRequiredIsFalse : publicationQidRequired ≡ false
    slrOutputCandidateOnly : Bool
    slrOutputCandidateOnlyIsTrue : slrOutputCandidateOnly ≡ true
    reviewerAcceptanceStillNotAdmission : Bool
    reviewerAcceptanceStillNotAdmissionIsTrue :
      reviewerAcceptanceStillNotAdmission ≡ true
    sourceAuditAdmissionRemainsIndependent : Bool
    sourceAuditAdmissionRemainsIndependentIsTrue :
      sourceAuditAdmissionRemainsIndependent ≡ true

open DigitalESDSLRBridgeBoundary public

canonicalDigitalESDSLRBridgeBoundary : DigitalESDSLRBridgeBoundary
canonicalDigitalESDSLRBridgeBoundary =
  digital-esd-slr-bridge-boundary
    true refl
    true refl
    false refl
    true refl
    true refl
    true refl

digitalESDSLRBridgeReading : String
digitalESDSLRBridgeReading =
  "Digital-ESD uses SensibLaw/SLR only after search lineage and screening have identified a source for full-text review. Full-text artifacts are same-object welded to the AttributedSource through explicit identifiers, artifact hashes and a reviewed identity reference; title equality is insufficient and publication QIDs are not required or invented. SLR/SensibLaw source-unit, parser, PNF, claim, tension and residual products remain candidate/review surfaces. They may propose source-indexed situated audit observations, but neither extraction nor reviewer acceptance constructs SourceAuditAdmission, raises the source claim ceiling, creates corpus inclusion or turns a claim candidate into paper truth. A final SLRAssistedCorpusAuditedSource exists only by pairing an already-constructed CorpusAuditedSource with the same-source SLR review packet; the sidecar cannot create admission."
