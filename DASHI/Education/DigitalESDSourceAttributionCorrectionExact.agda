module DASHI.Education.DigitalESDSourceAttributionCorrectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Legacy

------------------------------------------------------------------------
-- SOURCE ATTRIBUTION CORRECTIONS / NORMALISATIONS
--
-- Pinzone DOI: publisher metadata identifies Marta Pinzone, Francesca Sarti,
-- and Elisa Amodeo. The earlier feature-branch acquisition object retained
-- incorrect co-author given names.
--
-- Braßler DOI: the existing feature-branch object uses the ASCII transliteration
-- "Mirjam Brassler". This is retained as an identity ancestor, not called a
-- wrong-person attribution. New exact extraction uses the publisher's displayed
-- spelling "Mirjam Braßler".
------------------------------------------------------------------------

pinzoneEducationLCACorrectedSource : Attr.AttributedSource
pinzoneEducationLCACorrectedSource =
  Attr.mkDOISource
    "Marta Pinzone; Francesca Sarti; Elisa Amodeo"
    "What is the environmental impact of digitally enhanced education? Findings from a life cycle assessment of educational scenarios at an Italian university"
    "The International Journal of Life Cycle Assessment 31, article 112"
    "2026"
    "10.1007/s11367-026-02656-7"
    "https://doi.org/10.1007/s11367-026-02656-7"
    Attr.academicArticleSource
    "Corrected publisher-grounded source object for the education-scenario LCA comparing face-to-face, hybrid and online higher-education scenarios. Supports source-bounded LCA method, scenario-impact and uncertainty claims only; does not establish universal superiority of one delivery mode or a same-object footprint for another deployment."
    Attr.publicAttribution

legacyPinzoneSourceObject : Attr.AttributedSource
legacyPinzoneSourceObject = Legacy.pinzoneEducationLCASource

brasslerOERESDPublisherSpellingSource : Attr.AttributedSource
brasslerOERESDPublisherSpellingSource =
  Attr.mkDOISource
    "Mirjam Braßler"
    "Students' Digital Competence Development in the Production of Open Educational Resources in Education for Sustainable Development"
    "Sustainability 16(4), 1674"
    "2024"
    "10.3390/su16041674"
    "https://doi.org/10.3390/su16041674"
    Attr.academicArticleSource
    "Publisher-spelling source object for the two-group pretest-posttest OER/HESD study. The pre-existing ASCII transliteration remains an identity ancestor; this object is used for exact new extraction and does not by itself upgrade the study's quasi-experimental claim ceiling."
    Attr.publicAttribution

legacyBrasslerSourceObject : Attr.AttributedSource
legacyBrasslerSourceObject = Legacy.brasslerOERESDStudentProducerSource

record AttributionCorrectionBoundary : Set where
  constructor attributionCorrectionBoundary
  field
    exactDOIRetained : Bool
    exactDOIRetainedIsTrue : exactDOIRetained ≡ true
    correctedPublisherAuthorsRetained : Bool
    correctedPublisherAuthorsRetainedIsTrue : correctedPublisherAuthorsRetained ≡ true
    legacyObjectRetainedAsCorrectionProvenance : Bool
    legacyObjectRetainedAsCorrectionProvenanceIsTrue :
      legacyObjectRetainedAsCorrectionProvenance ≡ true
    legacyPinzoneAuthorMetadataMayBeUsedForNewExtraction : Bool
    legacyPinzoneAuthorMetadataMayBeUsedForNewExtractionIsFalse :
      legacyPinzoneAuthorMetadataMayBeUsedForNewExtraction ≡ false
    brasslerPublisherOrthographyRetainedForNewExtraction : Bool
    brasslerPublisherOrthographyRetainedForNewExtractionIsTrue :
      brasslerPublisherOrthographyRetainedForNewExtraction ≡ true
    legacyBrasslerASCIIIdentityMayRemainAsAncestor : Bool
    legacyBrasslerASCIIIdentityMayRemainAsAncestorIsTrue :
      legacyBrasslerASCIIIdentityMayRemainAsAncestor ≡ true
    DOIIdentityAutomaticallyRepairsMetadata : Bool
    DOIIdentityAutomaticallyRepairsMetadataIsFalse :
      DOIIdentityAutomaticallyRepairsMetadata ≡ false

open AttributionCorrectionBoundary public

canonicalAttributionCorrectionBoundary : AttributionCorrectionBoundary
canonicalAttributionCorrectionBoundary =
  attributionCorrectionBoundary
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl

attributionCorrectionReading : String
attributionCorrectionReading =
  "The Pinzone education-LCA DOI remains the same source identity, but the feature-branch acquisition object carried incorrect co-author given names; new extraction therefore uses Marta Pinzone, Francesca Sarti, and Elisa Amodeo. The Braßler OER/HESD source is the same DOI/person as the existing ASCII-transliterated Brassler object, but exact new extraction retains the publisher-displayed spelling Mirjam Braßler. DOI identity does not make every attached metadata field automatically correct, and correction/normalisation ancestry remains explicit."
