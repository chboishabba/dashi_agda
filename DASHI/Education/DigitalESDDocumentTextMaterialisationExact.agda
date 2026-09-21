module DASHI.Education.DigitalESDDocumentTextMaterialisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDSelectiveFullTextMaterialisationExact as Sparse

------------------------------------------------------------------------
-- DERIVED DOCUMENT TEXT MATERIALISATION
--
-- Runtime owner:
--   chboishabba/slr :: interop_scripts/document_text.py
--
-- The retained source artifact remains the canonical source identity.
-- Text extraction creates a derived carrier with its own digest and extractor
-- receipt.  It is a transport/materialisation step, not semantic payment.
------------------------------------------------------------------------

data DocumentFormat : Set where
  plaintext
  markdown
  html
  csv
  latex
  docx
  pdf
  : DocumentFormat

record DocumentTextAnchor : Set where
  constructor document-text-anchor
  field
    anchorReference : String
    extractedTextStartReference : String
    extractedTextEndReference : String
    pageReference : String
    paragraphReference : String

open DocumentTextAnchor public

record DocumentTextMaterialisationReceipt : Set where
  constructor document-text-materialisation-receipt
  field
    cacheReceipt : Sparse.FullTextCacheReceipt

    sourceArtifactReference : String
    sourceArtifactSha256 : String
    sourceArtifactSha256MatchesCache :
      sourceArtifactSha256
      ≡ Sparse.artifactSha256 cacheReceipt

    sourceFormat : DocumentFormat
    extractionEngine : String
    extractionEngineVersion : String

    extractedTextReference : String
    extractedTextSha256 : String
    extractedCharacterCount : Nat
    pageCountReference : String
    paragraphCountReference : String
    anchorManifestReference : String

    sourceArtifactRemainsIdentity : Bool
    sourceArtifactRemainsIdentityIsTrue :
      sourceArtifactRemainsIdentity ≡ true

    extractedTextIsDerivedCarrier : Bool
    extractedTextIsDerivedCarrierIsTrue :
      extractedTextIsDerivedCarrier ≡ true

    rawBinaryReadAsUtf8 : Bool
    rawBinaryReadAsUtf8IsFalse :
      rawBinaryReadAsUtf8 ≡ false

    implicitOCRUsed : Bool
    implicitOCRUsedIsFalse :
      implicitOCRUsed ≡ false

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false

    createsStudyTruth : Bool
    createsStudyTruthIsFalse :
      createsStudyTruth ≡ false

    createsSourceAuditAdmission : Bool
    createsSourceAuditAdmissionIsFalse :
      createsSourceAuditAdmission ≡ false

open DocumentTextMaterialisationReceipt public

------------------------------------------------------------------------
-- Scholarly parse receipt must consume the derived-text carrier while still
-- naming the original source revision/digest.
------------------------------------------------------------------------

record DerivedTextScholarlyParseReceipt : Set where
  constructor derived-text-scholarly-parse-receipt
  field
    materialisation : DocumentTextMaterialisationReceipt

    sourceRevisionReference : String
    sourceArtifactSha256 : String
    sourceArtifactSha256MatchesMaterialisation :
      sourceArtifactSha256
      ≡ DocumentTextMaterialisationReceipt.sourceArtifactSha256 materialisation

    extractedTextSha256 : String
    extractedTextSha256MatchesMaterialisation :
      extractedTextSha256
      ≡ DocumentTextMaterialisationReceipt.extractedTextSha256 materialisation

    parserReference : String
    parseBundleReference : String
    documentNodeCount : Nat
    studyFacetCount : Nat

    parserConsumesDerivedText : Bool
    parserConsumesDerivedTextIsTrue :
      parserConsumesDerivedText ≡ true

    parserConsumesRawBinary : Bool
    parserConsumesRawBinaryIsFalse :
      parserConsumesRawBinary ≡ false

    candidateOnly : Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true

    createsStudyTruth : Bool
    createsStudyTruthIsFalse :
      createsStudyTruth ≡ false

    createsSourceAuditAdmission : Bool
    createsSourceAuditAdmissionIsFalse :
      createsSourceAuditAdmission ≡ false

open DerivedTextScholarlyParseReceipt public

------------------------------------------------------------------------
-- Fail-closed extraction residual.
------------------------------------------------------------------------

record DocumentExtractionResidual : Set where
  constructor document-extraction-residual
  field
    sourceIdentityReference : String
    sourceRevisionReference : String
    artifactReference : String
    sourceFormatReference : String
    failureReference : String

    ocrRequired : Bool
    parserMayProceed : Bool
    parserMayProceedIsFalse :
      parserMayProceed ≡ false

    createsAutomaticOCRPermission : Bool
    createsAutomaticOCRPermissionIsFalse :
      createsAutomaticOCRPermission ≡ false

open DocumentExtractionResidual public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RawBinaryArtifactParsedAsUtf8 : Set where
data ImplicitOCRCreatesTrustedText : Set where
data DerivedTextDigestReplacesSourceArtifactDigest : Set where
data TextMaterialisationCreatesSemanticAuthority : Set where
data TextMaterialisationCreatesStudyTruth : Set where
data TextMaterialisationCreatesSourceAuditAdmission : Set where
data EmptyPDFTextCreatesSuccessfulParse : Set where
data ExtractorVersionCreatesSourceRevision : Set where

rawBinaryArtifactDoesNotParseAsUtf8 :
  RawBinaryArtifactParsedAsUtf8 → ⊥
rawBinaryArtifactDoesNotParseAsUtf8 ()

implicitOCRDoesNotCreateTrustedText :
  ImplicitOCRCreatesTrustedText → ⊥
implicitOCRDoesNotCreateTrustedText ()

derivedTextDigestDoesNotReplaceSourceArtifactDigest :
  DerivedTextDigestReplacesSourceArtifactDigest → ⊥
derivedTextDigestDoesNotReplaceSourceArtifactDigest ()

textMaterialisationDoesNotCreateSemanticAuthority :
  TextMaterialisationCreatesSemanticAuthority → ⊥
textMaterialisationDoesNotCreateSemanticAuthority ()

textMaterialisationDoesNotCreateStudyTruth :
  TextMaterialisationCreatesStudyTruth → ⊥
textMaterialisationDoesNotCreateStudyTruth ()

textMaterialisationDoesNotCreateSourceAuditAdmission :
  TextMaterialisationCreatesSourceAuditAdmission → ⊥
textMaterialisationDoesNotCreateSourceAuditAdmission ()

emptyPDFTextDoesNotCreateSuccessfulParse :
  EmptyPDFTextCreatesSuccessfulParse → ⊥
emptyPDFTextDoesNotCreateSuccessfulParse ()

extractorVersionDoesNotCreateSourceRevision :
  ExtractorVersionCreatesSourceRevision → ⊥
extractorVersionDoesNotCreateSourceRevision ()

record DocumentTextMaterialisationBoundary : Set where
  constructor document-text-materialisation-boundary
  field
    sourceArtifactRemainsCanonicalIdentity : Bool
    sourceArtifactRemainsCanonicalIdentityIsTrue :
      sourceArtifactRemainsCanonicalIdentity ≡ true

    extractedTextHasIndependentDigest : Bool
    extractedTextHasIndependentDigestIsTrue :
      extractedTextHasIndependentDigest ≡ true

    extractorIdentityRetained : Bool
    extractorIdentityRetainedIsTrue :
      extractorIdentityRetained ≡ true

    pageOrParagraphAnchorsRetained : Bool
    pageOrParagraphAnchorsRetainedIsTrue :
      pageOrParagraphAnchorsRetained ≡ true

    binaryArtifactsRequireExtraction : Bool
    binaryArtifactsRequireExtractionIsTrue :
      binaryArtifactsRequireExtraction ≡ true

    implicitOCREnabled : Bool
    implicitOCREnabledIsFalse :
      implicitOCREnabled ≡ false

    emptyExtractionMayProceed : Bool
    emptyExtractionMayProceedIsFalse :
      emptyExtractionMayProceed ≡ false

    textMaterialisationIsSemanticPayment : Bool
    textMaterialisationIsSemanticPaymentIsFalse :
      textMaterialisationIsSemanticPayment ≡ false

open DocumentTextMaterialisationBoundary public

canonicalDocumentTextMaterialisationBoundary :
  DocumentTextMaterialisationBoundary
canonicalDocumentTextMaterialisationBoundary =
  document-text-materialisation-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

documentTextMaterialisationReading : String
documentTextMaterialisationReading =
  "Retained Digital-ESD full-text bytes remain the canonical source artifact/revision identity. Binary PDF/DOCX artifacts must first lower through an explicit text-materialisation receipt carrying extractor identity/version, an independent extracted-text digest and exact derived anchors. The scholarly parser consumes only the derived text carrier, never raw binary bytes. Empty/image-only PDF extraction fails closed and does not trigger implicit OCR. Text extraction creates neither semantic authority, study truth nor SourceAuditAdmission."
