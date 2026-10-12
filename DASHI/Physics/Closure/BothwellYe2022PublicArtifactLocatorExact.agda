module DASHI.Physics.Closure.BothwellYe2022PublicArtifactLocatorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.BothwellYe2022MillimetreRedshiftReceipt as Source
import DASHI.Physics.Closure.QuantumClockEmpiricalRedshiftReceiptRequest as Request

------------------------------------------------------------------------
-- Stable public-artifact locator for Bothwell et al. 2022.
--
-- NIST exposes a publication record and a local-download PDF for the Nature
-- article.  This pays two generic evidence coordinates that are weaker than
-- byte-integrity:
--
--   * source artifact identity / stable locator;
--   * explicit access date.
--
-- The current execution environment can inspect the PDF through the public
-- source surface but cannot obtain its byte stream for a local digest.  The
-- artifact SHA-256 therefore remains false.  The publication PDF is also not
-- silently reclassified as the underlying experimental arrays or analysis
-- code; Nature explicitly says those are available from the corresponding
-- authors on reasonable request.
------------------------------------------------------------------------

record PublicExperimentArtifactLocator : Set where
  field
    artifactLabel : String
    articleDoi : String
    nistPublicationRecordUri : String
    nistLocalPdfUri : String
    publisherArticleUri : String
    accessDate : String
    expectedMediaType : String

    experimentArtifactIdentityIngested : Bool
    experimentArtifactIdentityIngestedIsTrue :
      experimentArtifactIdentityIngested ≡ true

    sourceAccessDateIngested : Bool
    sourceAccessDateIngestedIsTrue :
      sourceAccessDateIngested ≡ true

    experimentArtifactByteChecksumIngested : Bool
    experimentArtifactByteChecksumIngestedIsFalse :
      experimentArtifactByteChecksumIngested ≡ false

    rawExperimentArraysInArtifact : Bool
    rawExperimentArraysInArtifactIsFalse :
      rawExperimentArraysInArtifact ≡ false

    analysisCodeInArtifact : Bool
    analysisCodeInArtifactIsFalse :
      analysisCodeInArtifact ≡ false

    publicationArtifactIsRawExperimentDataset : Bool
    publicationArtifactIsRawExperimentDatasetIsFalse :
      publicationArtifactIsRawExperimentDataset ≡ false

    publicationArtifactIsAnalysisCodeBundle : Bool
    publicationArtifactIsAnalysisCodeBundleIsFalse :
      publicationArtifactIsAnalysisCodeBundle ≡ false

    locatorDischargesGenericAcceptanceToken : Bool
    locatorDischargesGenericAcceptanceTokenIsFalse :
      locatorDischargesGenericAcceptanceToken ≡ false

    reading : List String

open PublicExperimentArtifactLocator public

canonicalBothwellYe2022PublicArtifactLocator :
  PublicExperimentArtifactLocator
canonicalBothwellYe2022PublicArtifactLocator = record
  { artifactLabel =
      "Bothwell et al. 2022 Nature version-of-record publication artifact via NIST local download"
  ; articleDoi =
      "10.1038/s41586-021-04349-7"
  ; nistPublicationRecordUri =
      "https://www.nist.gov/publications/resolving-gravitational-redshift-across-millimetre-scale-atomic-sample"
  ; nistLocalPdfUri =
      "https://tsapps.nist.gov/publication/get_pdf.cfm?pub_id=933368"
  ; publisherArticleUri =
      "https://www.nature.com/articles/s41586-021-04349-7"
  ; accessDate =
      "2026-10-12"
  ; expectedMediaType =
      "application/pdf"
  ; experimentArtifactIdentityIngested = true
  ; experimentArtifactIdentityIngestedIsTrue = refl
  ; sourceAccessDateIngested = true
  ; sourceAccessDateIngestedIsTrue = refl
  ; experimentArtifactByteChecksumIngested = false
  ; experimentArtifactByteChecksumIngestedIsFalse = refl
  ; rawExperimentArraysInArtifact = false
  ; rawExperimentArraysInArtifactIsFalse = refl
  ; analysisCodeInArtifact = false
  ; analysisCodeInArtifactIsFalse = refl
  ; publicationArtifactIsRawExperimentDataset = false
  ; publicationArtifactIsRawExperimentDatasetIsFalse = refl
  ; publicationArtifactIsAnalysisCodeBundle = false
  ; publicationArtifactIsAnalysisCodeBundleIsFalse = refl
  ; locatorDischargesGenericAcceptanceToken = false
  ; locatorDischargesGenericAcceptanceTokenIsFalse = refl
  ; reading =
      "The DOI, NIST publication record and NIST local-download PDF identify a stable public publication artifact for the Bothwell/Ye experiment."
      ∷ "The access date is explicit rather than implicit in repository history."
      ∷ "No byte checksum is fabricated when the current execution path cannot acquire the PDF byte stream for hashing."
      ∷ "The publication artifact is distinct from the experimental arrays and analysis code, which remain author-request evidence."
      ∷ []
  }

canonicalExperimentArtifactIdentityIngested :
  experimentArtifactIdentityIngested canonicalBothwellYe2022PublicArtifactLocator ≡ true
canonicalExperimentArtifactIdentityIngested = refl

canonicalExperimentSourceAccessDateIngested :
  sourceAccessDateIngested canonicalBothwellYe2022PublicArtifactLocator ≡ true
canonicalExperimentSourceAccessDateIngested = refl

canonicalExperimentArtifactChecksumStillOpen :
  experimentArtifactByteChecksumIngested canonicalBothwellYe2022PublicArtifactLocator ≡ false
canonicalExperimentArtifactChecksumStillOpen = refl

------------------------------------------------------------------------
-- Explicit attachment to the existing generic request and original source
-- owner.  The attachment is navigational/provenance, not an acceptance token.
------------------------------------------------------------------------

record PublicArtifactRequestAttachment : Set where
  field
    originalSource : Source.BothwellYe2022Source
    originalSourceIsCanonical : originalSource ≡ Source.canonicalBothwellYe2022Source
    genericRequest : Request.QuantumClockEmpiricalRedshiftReceiptRequest
    genericRequestIsCanonical : genericRequest ≡ Request.canonicalQuantumClockEmpiricalRedshiftReceiptRequest
    locator : PublicExperimentArtifactLocator
    locatorIsCanonical : locator ≡ canonicalBothwellYe2022PublicArtifactLocator

canonicalPublicArtifactRequestAttachment : PublicArtifactRequestAttachment
canonicalPublicArtifactRequestAttachment = record
  { originalSource = Source.canonicalBothwellYe2022Source
  ; originalSourceIsCanonical = refl
  ; genericRequest = Request.canonicalQuantumClockEmpiricalRedshiftReceiptRequest
  ; genericRequestIsCanonical = refl
  ; locator = canonicalBothwellYe2022PublicArtifactLocator
  ; locatorIsCanonical = refl
  }
