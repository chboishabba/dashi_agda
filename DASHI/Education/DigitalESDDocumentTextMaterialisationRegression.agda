module DASHI.Education.DigitalESDDocumentTextMaterialisationRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDDocumentTextMaterialisationExact as Text

rawPdfCannotBeParsedAsUtf8 :
  Text.RawBinaryArtifactParsedAsUtf8 → ⊥
rawPdfCannotBeParsedAsUtf8 =
  Text.rawBinaryArtifactDoesNotParseAsUtf8

implicitOcrCannotCreateText :
  Text.ImplicitOCRCreatesTrustedText → ⊥
implicitOcrCannotCreateText =
  Text.implicitOCRDoesNotCreateTrustedText

derivedDigestCannotReplaceSourceDigest :
  Text.DerivedTextDigestReplacesSourceArtifactDigest → ⊥
derivedDigestCannotReplaceSourceDigest =
  Text.derivedTextDigestDoesNotReplaceSourceArtifactDigest

textMaterialisationCannotCreateStudyTruth :
  Text.TextMaterialisationCreatesStudyTruth → ⊥
textMaterialisationCannotCreateStudyTruth =
  Text.textMaterialisationDoesNotCreateStudyTruth

textMaterialisationCannotCreateAuditAdmission :
  Text.TextMaterialisationCreatesSourceAuditAdmission → ⊥
textMaterialisationCannotCreateAuditAdmission =
  Text.textMaterialisationDoesNotCreateSourceAuditAdmission

emptyPdfCannotBecomeSuccessfulParse :
  Text.EmptyPDFTextCreatesSuccessfulParse → ⊥
emptyPdfCannotBecomeSuccessfulParse =
  Text.emptyPDFTextDoesNotCreateSuccessfulParse

sourceBytesRemainIdentity :
  Text.sourceArtifactRemainsCanonicalIdentity
    Text.canonicalDocumentTextMaterialisationBoundary
  ≡ true
sourceBytesRemainIdentity = refl

extractedTextHasOwnDigest :
  Text.extractedTextHasIndependentDigest
    Text.canonicalDocumentTextMaterialisationBoundary
  ≡ true
extractedTextHasOwnDigest = refl
