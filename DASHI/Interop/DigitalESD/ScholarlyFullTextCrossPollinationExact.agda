module DASHI.Interop.DigitalESD.ScholarlyFullTextCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDERICStudyInteropExact as ERIC
import DASHI.Education.DigitalESDSelectiveFullTextMaterialisationExact as FullText
import DASHI.Education.DigitalESDSLRInteropWrapperExact as Wrapper
import DASHI.Education.DigitalESDStudyProcessingCensusExact as Census
import DASHI.Education.DigitalESDSituatedAuditObserverExact as Situated
import DASHI.Education.DigitalESDSourceAuditAdmissionExact as Audit
import DASHI.Interop.SLRCanonicalEvidenceSubstrateExact as Canonical

------------------------------------------------------------------------
-- DIGITAL-ESD SCHOLARLY FULL-TEXT CROSS-POLLINATION CONTRACT
--
-- Purpose:
--   compose existing Digital-ESD + SLR Agda owners into the ESD-4 contract
--   that thin interop wrappers must implement.
--
-- This module does NOT define a Digital-ESD paper parser.
--
-- The generic semantic path is:
--
--   retained full-text artifact
--      -> canonical manifestation
--      -> exact source revision
--      -> addressable document structure
--      -> generic scholarly facet candidate
--      -> canonical EvidenceObservation
--      -> explicit review
--      -> Digital-ESD situated audit projection
--
-- Digital-ESD owns only the consumer projection/admission semantics.
------------------------------------------------------------------------

ericMetadataBoundary : ERIC.ERICStudyInteropBoundary
ericMetadataBoundary = ERIC.canonicalERICStudyInteropBoundary

sparseFullTextBoundary : FullText.SparseMaterialisationBoundary
sparseFullTextBoundary = FullText.canonicalSparseMaterialisationBoundary

slrInteropBoundary : Wrapper.DigitalESDSLRInteropBoundary
slrInteropBoundary = Wrapper.canonicalDigitalESDSLRInteropBoundary

studyProcessingBoundary : Census.StudyProcessingCensusBoundary
studyProcessingBoundary = Census.canonicalStudyProcessingCensusBoundary

canonicalEvidenceBoundary : Canonical.SLRCanonicalEvidenceBoundary
canonicalEvidenceBoundary = Canonical.canonicalSLRCanonicalEvidenceBoundary

------------------------------------------------------------------------
-- Exact scholarly artifact -> canonical evidence identity.
------------------------------------------------------------------------

record ScholarlyFullTextCanonicalCarrier
    (source : Attr.AttributedSource) : Set where
  constructor scholarly-fulltext-canonical-carrier
  field
    attributedSource : Attr.AttributedSource
    attributedSourceIsSame : attributedSource ≡ source

    cacheReceipt : FullText.FullTextCacheReceipt
    sourceIdentityWeldReference : String

    canonicalManifestation : Canonical.EvidenceManifestation
    canonicalRevision : Canonical.EvidenceSourceRevision

    manifestationRevisionMatchesArtifact :
      Canonical.manifestationSourceRevisionRef canonicalManifestation
      ≡ FullText.sourceRevisionReference cacheReceipt

    manifestationDigestMatchesArtifact :
      Canonical.manifestationContentDigestRef canonicalManifestation
      ≡ FullText.artifactSha256 cacheReceipt

    canonicalRevisionMatchesManifestation :
      Canonical.revisionSourceRevisionRef canonicalRevision
      ≡ Canonical.manifestationSourceRevisionRef canonicalManifestation

    canonicalRevisionManifestationMatches :
      Canonical.revisionManifestationRef canonicalRevision
      ≡ Canonical.manifestationRef canonicalManifestation

    canonicalRevisionDigestMatches :
      Canonical.revisionContentDigestRef canonicalRevision
      ≡ Canonical.manifestationContentDigestRef canonicalManifestation

    artifactIdentityReviewed : Bool
    artifactIdentityReviewedIsTrue : artifactIdentityReviewed ≡ true

    artifactCreatesSemanticObservation : Bool
    artifactCreatesSemanticObservationIsFalse :
      artifactCreatesSemanticObservation ≡ false

open ScholarlyFullTextCanonicalCarrier public

------------------------------------------------------------------------
-- Generic document structure over one exact revision.
------------------------------------------------------------------------

data ScholarlyDocumentNodeKind : Set where
  documentSection
  heading
  paragraph
  sentence
  table
  tableCell
  figure
  figureCaption
  referenceEntry
  appendix
  otherDocumentNode
  : ScholarlyDocumentNodeKind

record ScholarlyDocumentStructureNode
    {source : Attr.AttributedSource}
    (artifact : ScholarlyFullTextCanonicalCarrier source) : Set where
  constructor scholarly-document-structure-node
  field
    nodeReference : String
    nodeKind : ScholarlyDocumentNodeKind
    anchor : Canonical.EvidenceSpan

    anchorRevisionMatchesArtifact :
      Canonical.spanSourceRevisionRef anchor
      ≡ Canonical.revisionSourceRevisionRef
          (ScholarlyFullTextCanonicalCarrier.canonicalRevision artifact)

    parserOrLayoutReceiptReference : String

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    createsClaimTruth : Bool
    createsClaimTruthIsFalse : createsClaimTruth ≡ false

    createsSourceAuditAdmission : Bool
    createsSourceAuditAdmissionIsFalse :
      createsSourceAuditAdmission ≡ false

open ScholarlyDocumentStructureNode public

------------------------------------------------------------------------
-- Generic scholarly-study semantics.
--
-- These are candidate roles, not Digital-ESD audit axes.
------------------------------------------------------------------------

data ScholarlyStudyFacetKind : Set where
  study
  population
  sample
  intervention
  comparator
  outcome
  studyDesign
  setting
  timePeriod
  method
  limitation
  funding
  institution
  participantGroup
  measurement
  otherStudyFacet
  : ScholarlyStudyFacetKind

record ScholarlyStudyFacetCandidate
    {source : Attr.AttributedSource}
    (artifact : ScholarlyFullTextCanonicalCarrier source) : Set where
  constructor scholarly-study-facet-candidate
  field
    facetReference : String
    facetKind : ScholarlyStudyFacetKind

    documentNode :
      ScholarlyDocumentStructureNode artifact

    canonicalObservation : Canonical.EvidenceObservation

    observationUsesNodeAnchor :
      Canonical.observationSpan canonicalObservation
      ≡ ScholarlyDocumentStructureNode.anchor documentNode

    observationRevisionWeld :
      Canonical.ObservationRevisionWeld canonicalObservation

    parserOrModelReceiptReference : String
    ontologyCandidateReference : String

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    createsStudyTruth : Bool
    createsStudyTruthIsFalse : createsStudyTruth ≡ false

    createsScreeningDecision : Bool
    createsScreeningDecisionIsFalse :
      createsScreeningDecision ≡ false

    createsSourceAuditAdmission : Bool
    createsSourceAuditAdmissionIsFalse :
      createsSourceAuditAdmission ≡ false

open ScholarlyStudyFacetCandidate public

------------------------------------------------------------------------
-- Review remains a separate payment.
------------------------------------------------------------------------

record ReviewedScholarlyStudyObservation
    {source : Attr.AttributedSource}
    (artifact : ScholarlyFullTextCanonicalCarrier source) : Set where
  constructor reviewed-scholarly-study-observation
  field
    candidate : ScholarlyStudyFacetCandidate artifact

    reviewReference : String
    paymentReference : String
    reviewerReference : String
    reviewReason : String

    reviewedCanonicalObservation :
      Canonical.EvidenceObservation

    reviewedObservationIsCandidateObservation :
      reviewedCanonicalObservation
      ≡ ScholarlyStudyFacetCandidate.canonicalObservation candidate

    reviewed : Bool
    reviewedIsTrue : reviewed ≡ true

    reviewCreatesClaimTruth : Bool
    reviewCreatesClaimTruthIsFalse :
      reviewCreatesClaimTruth ≡ false

    reviewCreatesSourceAuditAdmission : Bool
    reviewCreatesSourceAuditAdmissionIsFalse :
      reviewCreatesSourceAuditAdmission ≡ false

open ReviewedScholarlyStudyObservation public

------------------------------------------------------------------------
-- Digital-ESD is a consumer projection over reviewed canonical evidence.
------------------------------------------------------------------------

record DigitalESDAuditProjectionReceipt
    {source : Attr.AttributedSource}
    {artifact : ScholarlyFullTextCanonicalCarrier source}
    (reviewedObservation : ReviewedScholarlyStudyObservation artifact) : Set where
  constructor digital-esd-audit-projection-receipt
  field
    projectionReference : String

    canonicalObservation :
      Canonical.EvidenceObservation

    canonicalObservationPreserved :
      canonicalObservation
      ≡ ReviewedScholarlyStudyObservation.reviewedCanonicalObservation
          reviewedObservation

    situatedAuditObservation : Situated.SituatedAuditObservation

    situatedSourceIsSame :
      Situated.source situatedAuditObservation ≡ source

    supportingCanonicalObservationReference : String
    consumerQuestionReference : String

    projectionCreatesCanonicalEvidence : Bool
    projectionCreatesCanonicalEvidenceIsFalse :
      projectionCreatesCanonicalEvidence ≡ false

    projectionCreatesSourceAuditAdmission : Bool
    projectionCreatesSourceAuditAdmissionIsFalse :
      projectionCreatesSourceAuditAdmission ≡ false

open DigitalESDAuditProjectionReceipt public

------------------------------------------------------------------------
-- Audit admission remains independently paid.
------------------------------------------------------------------------

record ProjectedStudyAuditCarrier
    (source : Attr.AttributedSource) : Set where
  constructor projected-study-audit-carrier
  field
    projectionReference : String
    sourceAuditAdmission : Audit.SourceAuditAdmission source
    auditAdmissionReference : String

open ProjectedStudyAuditCarrier public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ERICMetadataCreatesParsedStudy : Set where
data FullTextArtifactCreatesSemanticObservation : Set where
data DocumentStructureCreatesClaimTruth : Set where
data DocumentStructureCreatesStudyTruth : Set where
data StudyFacetCandidateCreatesStudyTruth : Set where
data StudyFacetCandidateCreatesScreeningDecision : Set where
data ReviewedStudyObservationCreatesClaimTruth : Set where
data ReviewedStudyObservationCreatesSourceAuditAdmission : Set where
data DigitalESDProjectionMayReplaceCanonicalObservation : Set where
data DigitalESDProjectionCreatesCanonicalEvidence : Set where
data DigitalESDProjectionCreatesSourceAuditAdmission : Set where
data StructuredDocumentNodeRequiresFakeTextRange : Set where
data WholeRevisionNodeRequiresFakeTextRange : Set where
data ParserSuccessCreatesReviewPayment : Set where
data ParserModelCreatesSourceAuthority : Set where

ericMetadataDoesNotCreateParsedStudy :
  ERICMetadataCreatesParsedStudy → ⊥
ericMetadataDoesNotCreateParsedStudy ()

fullTextArtifactDoesNotCreateSemanticObservation :
  FullTextArtifactCreatesSemanticObservation → ⊥
fullTextArtifactDoesNotCreateSemanticObservation ()

documentStructureDoesNotCreateClaimTruth :
  DocumentStructureCreatesClaimTruth → ⊥
documentStructureDoesNotCreateClaimTruth ()

documentStructureDoesNotCreateStudyTruth :
  DocumentStructureCreatesStudyTruth → ⊥
documentStructureDoesNotCreateStudyTruth ()

studyFacetCandidateDoesNotCreateStudyTruth :
  StudyFacetCandidateCreatesStudyTruth → ⊥
studyFacetCandidateDoesNotCreateStudyTruth ()

studyFacetCandidateDoesNotCreateScreeningDecision :
  StudyFacetCandidateCreatesScreeningDecision → ⊥
studyFacetCandidateDoesNotCreateScreeningDecision ()

reviewedStudyObservationDoesNotCreateClaimTruth :
  ReviewedStudyObservationCreatesClaimTruth → ⊥
reviewedStudyObservationDoesNotCreateClaimTruth ()

reviewedStudyObservationDoesNotCreateSourceAuditAdmission :
  ReviewedStudyObservationCreatesSourceAuditAdmission → ⊥
reviewedStudyObservationDoesNotCreateSourceAuditAdmission ()

digitalESDProjectionDoesNotReplaceCanonicalObservation :
  DigitalESDProjectionMayReplaceCanonicalObservation → ⊥
digitalESDProjectionDoesNotReplaceCanonicalObservation ()

digitalESDProjectionDoesNotCreateCanonicalEvidence :
  DigitalESDProjectionCreatesCanonicalEvidence → ⊥
digitalESDProjectionDoesNotCreateCanonicalEvidence ()

digitalESDProjectionDoesNotCreateSourceAuditAdmission :
  DigitalESDProjectionCreatesSourceAuditAdmission → ⊥
digitalESDProjectionDoesNotCreateSourceAuditAdmission ()

structuredDocumentNodeDoesNotRequireFakeTextRange :
  StructuredDocumentNodeRequiresFakeTextRange → ⊥
structuredDocumentNodeDoesNotRequireFakeTextRange ()

wholeRevisionNodeDoesNotRequireFakeTextRange :
  WholeRevisionNodeRequiresFakeTextRange → ⊥
wholeRevisionNodeDoesNotRequireFakeTextRange ()

parserSuccessDoesNotCreateReviewPayment :
  ParserSuccessCreatesReviewPayment → ⊥
parserSuccessDoesNotCreateReviewPayment ()

parserModelDoesNotCreateSourceAuthority :
  ParserModelCreatesSourceAuthority → ⊥
parserModelDoesNotCreateSourceAuthority ()

------------------------------------------------------------------------
-- Thin-wrapper implementation boundary.
------------------------------------------------------------------------

record ScholarlyFullTextCrossPollinationBoundary : Set where
  constructor scholarly-fulltext-cross-pollination-boundary
  field
    ericMetadataStopsBeforeFullText : Bool
    ericMetadataStopsBeforeFullTextIsTrue :
      ericMetadataStopsBeforeFullText ≡ true

    fullTextRevisionDigestWeldRequired : Bool
    fullTextRevisionDigestWeldRequiredIsTrue :
      fullTextRevisionDigestWeldRequired ≡ true

    documentStructureUsesCanonicalSpans : Bool
    documentStructureUsesCanonicalSpansIsTrue :
      documentStructureUsesCanonicalSpans ≡ true

    genericStudyFacetLayerExists : Bool
    genericStudyFacetLayerExistsIsTrue :
      genericStudyFacetLayerExists ≡ true

    facetCandidateUsesCanonicalObservation : Bool
    facetCandidateUsesCanonicalObservationIsTrue :
      facetCandidateUsesCanonicalObservation ≡ true

    parserOutputCandidateOnly : Bool
    parserOutputCandidateOnlyIsTrue :
      parserOutputCandidateOnly ≡ true

    reviewSeparateFromParsing : Bool
    reviewSeparateFromParsingIsTrue :
      reviewSeparateFromParsing ≡ true

    digitalESDIsConsumerProjection : Bool
    digitalESDIsConsumerProjectionIsTrue :
      digitalESDIsConsumerProjection ≡ true

    sourceAuditAdmissionIndependent : Bool
    sourceAuditAdmissionIndependentIsTrue :
      sourceAuditAdmissionIndependent ≡ true

    wrapperMayOwnParserSemantics : Bool
    wrapperMayOwnParserSemanticsIsFalse :
      wrapperMayOwnParserSemantics ≡ false

    wrapperMayCreateTruth : Bool
    wrapperMayCreateTruthIsFalse :
      wrapperMayCreateTruth ≡ false

open ScholarlyFullTextCrossPollinationBoundary public

canonicalScholarlyFullTextCrossPollinationBoundary :
  ScholarlyFullTextCrossPollinationBoundary
canonicalScholarlyFullTextCrossPollinationBoundary =
  scholarly-fulltext-cross-pollination-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl

scholarlyFullTextCrossPollinationReading : String
scholarlyFullTextCrossPollinationReading =
  "Digital-ESD ESD-4 cross-pollinates existing ERIC metadata, sparse full-text materialisation, SLR interop, canonical evidence and source-audit owners without defining an ESD-specific paper parser. A retained full-text artifact must same-object weld its exact revision and digest to one canonical manifestation/revision. Parser/layout output is addressable document structure over canonical EvidenceSpan values; it creates no claim truth. Generic scholarly facet candidates (population, sample, intervention, comparator, outcome, design, setting, time, method, limitation, funding, institution, participant group, measurement) are canonical EvidenceObservation values anchored to exact document nodes and remain candidate-only. Review is an additional payment. Digital-ESD then consumes reviewed canonical observations through a SituatedAuditObservation projection; projection neither replaces canonical evidence nor constructs SourceAuditAdmission."
