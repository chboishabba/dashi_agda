module DASHI.Education.DigitalESDFullTextSLRParseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDSelectiveFullTextMaterialisationExact as Cache
import DASHI.Education.DigitalESDStudyProcessingCensusExact as Census

------------------------------------------------------------------------
-- VERIFIED FULL TEXT -> SLR PARSER HANDOFF
--
-- Runtime owner:
--   interop_scripts/digital_esd/run_verified_fulltext_parse.py
--
-- This module does not model the parser's internals.  It formalises only the
-- application-side same-object boundary:
--
--   verified cache receipt
--     -> parser request
--     -> normalized parser receipt
--
-- and preserves:
--
--   cache registration != parse
--   parse != reviewed canonical evidence
--   reviewed canonical evidence != SourceAuditAdmission
------------------------------------------------------------------------


------------------------------------------------------------------------
-- Binary/document artifact -> parser-text materialisation.
--
-- PDF/DOCX/HTML bytes and extracted UTF-8 text are distinct revisions.
-- The parser is forbidden from silently replacing one with the other.
------------------------------------------------------------------------

record TextMaterialisationReceipt : Set where
  constructor text-materialisation-receipt
  field
    materialisationSourceIdentityReference : String

    parentArtifactRevisionReference : String
    parentArtifactDigestReference : String
    parentArtifactReference : String

    materialisedTextRevisionReference : String
    materialisedTextDigestReference : String
    materialisedTextReference : String
    extractionBackendReference : String
    materialisationReceiptReference : String

    parentArtifactDigestRechecked : Bool
    parentArtifactDigestRecheckedIsTrue :
      parentArtifactDigestRechecked ≡ true

    derivedTextRevisionExplicit : Bool
    derivedTextRevisionExplicitIsTrue :
      derivedTextRevisionExplicit ≡ true

    materialisationCreatesSemanticAuthority : Bool
    materialisationCreatesSemanticAuthorityIsFalse :
      materialisationCreatesSemanticAuthority ≡ false

    materialisationCreatesReviewedEvidence : Bool
    materialisationCreatesReviewedEvidenceIsFalse :
      materialisationCreatesReviewedEvidence ≡ false

    materialisationCreatesSourceAuditAdmission : Bool
    materialisationCreatesSourceAuditAdmissionIsFalse :
      materialisationCreatesSourceAuditAdmission ≡ false

open TextMaterialisationReceipt public

record SLRParseRequest : Set where
  constructor slr-parse-request
  field
    sourceIdentityReference : String
    sourceRevisionReference : String
    contentDigestReference : String
    artifactReference : String
    acquisitionReceiptReference : String
    requestReference : String

    materialisation : TextMaterialisationReceipt

    requestIdentityMatchesMaterialisation :
      sourceIdentityReference
      ≡ materialisationSourceIdentityReference materialisation

    requestRevisionMatchesMaterialisedText :
      sourceRevisionReference
      ≡ materialisedTextRevisionReference materialisation

    requestDigestMatchesMaterialisedText :
      contentDigestReference
      ≡ materialisedTextDigestReference materialisation

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    cacheRegistrationCountsAsParse : Bool
    cacheRegistrationCountsAsParseIsFalse :
      cacheRegistrationCountsAsParse ≡ false

    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false

    createsSourceAuditAdmission : Bool
    createsSourceAuditAdmissionIsFalse :
      createsSourceAuditAdmission ≡ false

open SLRParseRequest public

record NormalizedSLRParseReceipt : Set where
  constructor normalized-slr-parse-receipt
  field
    sourceIdentityReference : String
    sourceRevisionReference : String
    contentDigestReference : String
    parseBundleReference : String
    documentNodeCountReference : String
    studyFacetCountReference : String
    parserReference : String
    parserRevisionReference : String
    receiptReference : String

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false

    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse :
      applicabilityPromoted ≡ false

    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse :
      claimTruthPromoted ≡ false

    createsReviewedCanonicalEvidence : Bool
    createsReviewedCanonicalEvidenceIsFalse :
      createsReviewedCanonicalEvidence ≡ false

    createsSourceAuditAdmission : Bool
    createsSourceAuditAdmissionIsFalse :
      createsSourceAuditAdmission ≡ false

open NormalizedSLRParseReceipt public

record SLRParseReconciliationReceipt : Set where
  constructor slr-parse-reconciliation-receipt
  field
    request : SLRParseRequest
    parserReceipt : NormalizedSLRParseReceipt

    sourceIdentityMatches : Bool
    sourceIdentityMatchesIsTrue :
      sourceIdentityMatches ≡ true

    sourceRevisionMatches : Bool
    sourceRevisionMatchesIsTrue :
      sourceRevisionMatches ≡ true

    contentDigestMatches : Bool
    contentDigestMatchesIsTrue :
      contentDigestMatches ≡ true

    artifactDigestRechecked : Bool
    artifactDigestRecheckedIsTrue :
      artifactDigestRechecked ≡ true

    parserOutputCandidateOnly : Bool
    parserOutputCandidateOnlyIsTrue :
      parserOutputCandidateOnly ≡ true

    documentStructureObserved : Bool
    documentStructureObservedIsTrue :
      documentStructureObserved ≡ true

    studyFacetsRemainCandidateOnly : Bool
    studyFacetsRemainCandidateOnlyIsTrue :
      studyFacetsRemainCandidateOnly ≡ true

    reconciliationCreatesReview : Bool
    reconciliationCreatesReviewIsFalse :
      reconciliationCreatesReview ≡ false

    reconciliationCreatesAdmission : Bool
    reconciliationCreatesAdmissionIsFalse :
      reconciliationCreatesAdmission ≡ false

open SLRParseReconciliationReceipt public

------------------------------------------------------------------------
-- Existing cache/census authorities remain distinct.
------------------------------------------------------------------------

cacheBoundary : Cache.SparseMaterialisationBoundary
cacheBoundary = Cache.canonicalSparseMaterialisationBoundary

censusBoundary : Census.StudyProcessingCensusBoundary
censusBoundary = Census.canonicalStudyProcessingCensusBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CacheRegistrationCountsAsSLRParse : Set where
data VerifiedFullTextCreatesReviewedCanonicalEvidence : Set where
data SLRParseCreatesReviewedCanonicalEvidence : Set where
data SLRParseCreatesSourceAuditAdmission : Set where
data SLRParseCreatesSourceTruth : Set where
data ParserProcessExitCreatesEvidencePayment : Set where
data ParserMayReplaceSourceRevision : Set where
data ParserMayReplaceContentDigest : Set where
data ParserMayReplaceSourceIdentity : Set where
data MetadataOnlyRowMayEnterParseHandoff : Set where
data TextMaterialisationCountsAsSLRParse : Set where
data TextMaterialisationMayEraseParentRevision : Set where
data ParserMayAnchorTextSpanToParentBinaryRevision : Set where

cacheRegistrationDoesNotCountAsSLRParse :
  CacheRegistrationCountsAsSLRParse → ⊥
cacheRegistrationDoesNotCountAsSLRParse ()

verifiedFullTextDoesNotCreateReviewedCanonicalEvidence :
  VerifiedFullTextCreatesReviewedCanonicalEvidence → ⊥
verifiedFullTextDoesNotCreateReviewedCanonicalEvidence ()

slrParseDoesNotCreateReviewedCanonicalEvidence :
  SLRParseCreatesReviewedCanonicalEvidence → ⊥
slrParseDoesNotCreateReviewedCanonicalEvidence ()

slrParseDoesNotCreateSourceAuditAdmission :
  SLRParseCreatesSourceAuditAdmission → ⊥
slrParseDoesNotCreateSourceAuditAdmission ()

slrParseDoesNotCreateSourceTruth :
  SLRParseCreatesSourceTruth → ⊥
slrParseDoesNotCreateSourceTruth ()

parserProcessExitDoesNotCreateEvidencePayment :
  ParserProcessExitCreatesEvidencePayment → ⊥
parserProcessExitDoesNotCreateEvidencePayment ()

parserDoesNotReplaceSourceRevision :
  ParserMayReplaceSourceRevision → ⊥
parserDoesNotReplaceSourceRevision ()

parserDoesNotReplaceContentDigest :
  ParserMayReplaceContentDigest → ⊥
parserDoesNotReplaceContentDigest ()

parserDoesNotReplaceSourceIdentity :
  ParserMayReplaceSourceIdentity → ⊥
parserDoesNotReplaceSourceIdentity ()

metadataOnlyRowDoesNotEnterParseHandoff :
  MetadataOnlyRowMayEnterParseHandoff → ⊥
metadataOnlyRowDoesNotEnterParseHandoff ()

textMaterialisationDoesNotCountAsSLRParse :
  TextMaterialisationCountsAsSLRParse → ⊥
textMaterialisationDoesNotCountAsSLRParse ()

textMaterialisationDoesNotEraseParentRevision :
  TextMaterialisationMayEraseParentRevision → ⊥
textMaterialisationDoesNotEraseParentRevision ()

parserDoesNotAnchorTextSpanToParentBinaryRevision :
  ParserMayAnchorTextSpanToParentBinaryRevision → ⊥
parserDoesNotAnchorTextSpanToParentBinaryRevision ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record FullTextSLRParseBoundary : Set where
  constructor fulltext-slr-parse-boundary
  field
    cacheLedgerIsParserInputAuthority : Bool
    cacheLedgerIsParserInputAuthorityIsTrue :
      cacheLedgerIsParserInputAuthority ≡ true

    materialisedArtifactRequired : Bool
    materialisedArtifactRequiredIsTrue :
      materialisedArtifactRequired ≡ true

    sameObjectIdentityRequired : Bool
    sameObjectIdentityRequiredIsTrue :
      sameObjectIdentityRequired ≡ true

    binaryAndMaterialisedTextRevisionsDistinct : Bool
    binaryAndMaterialisedTextRevisionsDistinctIsTrue :
      binaryAndMaterialisedTextRevisionsDistinct ≡ true

    derivedTextRevisionRequiresExplicitReceipt : Bool
    derivedTextRevisionRequiresExplicitReceiptIsTrue :
      derivedTextRevisionRequiresExplicitReceipt ≡ true

    parserAnchorsBelongToMaterialisedTextRevision : Bool
    parserAnchorsBelongToMaterialisedTextRevisionIsTrue :
      parserAnchorsBelongToMaterialisedTextRevision ≡ true

    artifactDigestRecheckedBeforeHandoff : Bool
    artifactDigestRecheckedBeforeHandoffIsTrue :
      artifactDigestRecheckedBeforeHandoff ≡ true

    parserOutputMustBeCandidateOnly : Bool
    parserOutputMustBeCandidateOnlyIsTrue :
      parserOutputMustBeCandidateOnly ≡ true

    cacheRegistrationIsParse : Bool
    cacheRegistrationIsParseIsFalse :
      cacheRegistrationIsParse ≡ false

    processExitIsEvidencePayment : Bool
    processExitIsEvidencePaymentIsFalse :
      processExitIsEvidencePayment ≡ false

    parseCreatesReviewedCanonicalEvidence : Bool
    parseCreatesReviewedCanonicalEvidenceIsFalse :
      parseCreatesReviewedCanonicalEvidence ≡ false

    parseCreatesSourceAuditAdmission : Bool
    parseCreatesSourceAuditAdmissionIsFalse :
      parseCreatesSourceAuditAdmission ≡ false

open FullTextSLRParseBoundary public

canonicalFullTextSLRParseBoundary : FullTextSLRParseBoundary
canonicalFullTextSLRParseBoundary =
  fulltext-slr-parse-boundary
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
    false refl
    false refl

fullTextSLRParseReading : String
fullTextSLRParseReading =
  "Digital-ESD full-text parsing begins only after an authoritative include/probable decision has led to a materialised cache artifact. The cache ledger is rechecked against the actual artifact digest before parser handoff. Binary/document bytes and their extracted UTF-8 parser text are distinct revisions: an explicit TextMaterialisationReceipt retains the parent artifact revision/digest and the derived text revision/digest. Parser text/span anchors belong to that derived text revision, never silently to the parent PDF/DOCX binary revision. The parser request and normalized parsed-bundle receipt must preserve the same source identity, exact parser-text revision and content digest. A parsed bundle may contain many anchored document nodes and candidate study facets; it is not itself a reviewed canonical EvidenceObservation. Cache registration is not parsing; a zero process exit is not evidence payment; parser bundles do not create reviewed canonical evidence, source truth or SourceAuditAdmission."
