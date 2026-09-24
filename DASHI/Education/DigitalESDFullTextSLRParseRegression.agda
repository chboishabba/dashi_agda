module DASHI.Education.DigitalESDFullTextSLRParseRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDFullTextSLRParseExact as Parse

cacheRegistrationCannotCountAsParse :
  Parse.CacheRegistrationCountsAsSLRParse → ⊥
cacheRegistrationCannotCountAsParse =
  Parse.cacheRegistrationDoesNotCountAsSLRParse

verifiedFullTextCannotCreateReviewedEvidence :
  Parse.VerifiedFullTextCreatesReviewedCanonicalEvidence → ⊥
verifiedFullTextCannotCreateReviewedEvidence =
  Parse.verifiedFullTextDoesNotCreateReviewedCanonicalEvidence

slrParseCannotCreateReviewedEvidence :
  Parse.SLRParseCreatesReviewedCanonicalEvidence → ⊥
slrParseCannotCreateReviewedEvidence =
  Parse.slrParseDoesNotCreateReviewedCanonicalEvidence

slrParseCannotCreateAuditAdmission :
  Parse.SLRParseCreatesSourceAuditAdmission → ⊥
slrParseCannotCreateAuditAdmission =
  Parse.slrParseDoesNotCreateSourceAuditAdmission

parseReceiptRequiresSameObjectIdentity :
  Parse.sameObjectIdentityRequired
    Parse.canonicalFullTextSLRParseBoundary
  ≡ true
parseReceiptRequiresSameObjectIdentity = refl

parseReceiptRequiresDigestRecheck :
  Parse.artifactDigestRecheckedBeforeHandoff
    Parse.canonicalFullTextSLRParseBoundary
  ≡ true
parseReceiptRequiresDigestRecheck = refl


binaryAndTextRevisionsRemainDistinct :
  Parse.binaryAndMaterialisedTextRevisionsDistinct
    Parse.canonicalFullTextSLRParseBoundary
  ≡ true
binaryAndTextRevisionsRemainDistinct = refl

derivedTextRevisionRequiresReceipt :
  Parse.derivedTextRevisionRequiresExplicitReceipt
    Parse.canonicalFullTextSLRParseBoundary
  ≡ true
derivedTextRevisionRequiresReceipt = refl

parserAnchorsUseMaterialisedTextRevision :
  Parse.parserAnchorsBelongToMaterialisedTextRevision
    Parse.canonicalFullTextSLRParseBoundary
  ≡ true
parserAnchorsUseMaterialisedTextRevision = refl

textMaterialisationCannotCountAsParse :
  Parse.TextMaterialisationCountsAsSLRParse → ⊥
textMaterialisationCannotCountAsParse =
  Parse.textMaterialisationDoesNotCountAsSLRParse

parserCannotAnchorTextToParentBinary :
  Parse.ParserMayAnchorTextSpanToParentBinaryRevision → ⊥
parserCannotAnchorTextToParentBinary =
  Parse.parserDoesNotAnchorTextSpanToParentBinaryRevision
