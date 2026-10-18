module DASHI.Education.DigitalESDSourceAttributionCorrectionRegression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Education.DigitalESDSourceAttributionCorrectionExact as Correction
import DASHI.Core.AttributedSourceCore as Attr

correctedPinzoneAuthorsRegression :
  Attr.AttributedSource.sourceAuthor Correction.pinzoneEducationLCACorrectedSource
  ≡ "Marta Pinzone; Francesca Sarti; Elisa Amodeo"
correctedPinzoneAuthorsRegression = refl

correctedPinzoneDOIRegression :
  Attr.AttributedSource.doiState Correction.pinzoneEducationLCACorrectedSource
  ≡ Attr.doiRecorded "10.1007/s11367-026-02656-7"
correctedPinzoneDOIRegression = refl

legacyAttributionSupersededRegression :
  Correction.AttributionCorrectionBoundary.legacyPinzoneAuthorMetadataMayBeUsedForNewExtraction
    Correction.canonicalAttributionCorrectionBoundary
  ≡ false
legacyAttributionSupersededRegression = refl

brasslerPublisherSpellingRegression :
  Attr.AttributedSource.sourceAuthor Correction.brasslerOERESDPublisherSpellingSource
  ≡ "Mirjam Braßler"
brasslerPublisherSpellingRegression = refl

brasslerDOIRegression :
  Attr.AttributedSource.doiState Correction.brasslerOERESDPublisherSpellingSource
  ≡ Attr.doiRecorded "10.3390/su16041674"
brasslerDOIRegression = refl

brasslerASCIIAncestorRetainedRegression :
  Correction.AttributionCorrectionBoundary.legacyBrasslerASCIIIdentityMayRemainAsAncestor
    Correction.canonicalAttributionCorrectionBoundary
  ≡ true
brasslerASCIIAncestorRetainedRegression = refl
