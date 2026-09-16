module DASHI.Education.DigitalESDSourceAttributionCorrectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Legacy

------------------------------------------------------------------------
-- SOURCE ATTRIBUTION CORRECTION
--
-- Publisher metadata for DOI 10.1007/s11367-026-02656-7 identifies the authors
-- as Marta Pinzone, Francesca Sarti, and Elisa Amodeo. The earlier acquisition
-- object on this feature branch retained incorrect co-author given names.
-- New extraction must use the corrected object below; the legacy object remains
-- reachable only as provenance of the repository correction event.
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
    false refl

attributionCorrectionReading : String
attributionCorrectionReading =
  "The Pinzone education-LCA DOI remains the same source identity, but the feature-branch acquisition object carried incorrect co-author given names. Publisher-grounded author metadata is corrected to Marta Pinzone, Francesca Sarti, and Elisa Amodeo. DOI identity does not retroactively make incorrect metadata correct; the legacy object is retained only as correction provenance and must not seed new extraction."
