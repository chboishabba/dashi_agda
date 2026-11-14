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
-- article. Redundant public discovery also found a JILA-hosted article PDF and
-- a University of Glasgow author-accepted manuscript. These pay resilient
-- artifact-location/provenance coordinates, not byte identity between mirrors.
--
-- The current execution environment can inspect public source surfaces but
-- cannot obtain a trustworthy local byte stream for hashing. Artifact SHA-256
-- therefore remains false. The publication PDFs are not silently reclassified
-- as the underlying experimental arrays or analysis code; Nature states that
-- those are available from the corresponding authors on reasonable request.
------------------------------------------------------------------------

record PublicExperimentArtifactLocator : Set where
  field
    artifactLabel : String
    articleDoi : String
    nistPublicationRecordUri : String
    nistLocalPdfUri : String
    publisherArticleUri : String
    jilaPublicPdfMirrorUri : String
    jilaMirrorRole : String
    glasgowAcceptedManuscriptUri : String
    glasgowMirrorRole : String
    accessDate : String
    mirrorDiscoveryDate : String
    expectedMediaType : String

    experimentArtifactIdentityIngested : Bool
    experimentArtifactIdentityIngestedIsTrue :
      experimentArtifactIdentityIngested ≡ true

    redundantPublicLocatorIngested : Bool
    redundantPublicLocatorIngestedIsTrue :
      redundantPublicLocatorIngested ≡ true

    sourceAccessDateIngested : Bool
    sourceAccessDateIngestedIsTrue :
      sourceAccessDateIngested ≡ true

    experimentArtifactByteChecksumIngested : Bool
    experimentArtifactByteChecksumIngestedIsFalse :
      experimentArtifactByteChecksumIngested ≡ false

    publicMirrorsAssertedByteIdentical : Bool
    publicMirrorsAssertedByteIdenticalIsFalse :
      publicMirrorsAssertedByteIdentical ≡ false

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
      "Bothwell et al. 2022 Nature publication artifact with redundant public locators"
  ; articleDoi =
      "10.1038/s41586-021-04349-7"
  ; nistPublicationRecordUri =
      "https://www.nist.gov/publications/resolving-gravitational-redshift-across-millimetre-scale-atomic-sample"
  ; nistLocalPdfUri =
      "https://tsapps.nist.gov/publication/get_pdf.cfm?pub_id=933368"
  ; publisherArticleUri =
      "https://www.nature.com/articles/s41586-021-04349-7"
  ; jilaPublicPdfMirrorUri =
      "https://jila.colorado.edu/sites/default/files/2022-02/Redshift%201%20mm_Nature%202022.pdf"
  ; jilaMirrorRole =
      "public PDF mirror of the Nature article"
  ; glasgowAcceptedManuscriptUri =
      "https://eprints.gla.ac.uk/264685/2/264685.pdf"
  ; glasgowMirrorRole =
      "author accepted manuscript; not asserted byte-identical to version of record"
  ; accessDate =
      "2026-10-12"
  ; mirrorDiscoveryDate =
      "2026-10-16"
  ; expectedMediaType =
      "application/pdf"
  ; experimentArtifactIdentityIngested = true
  ; experimentArtifactIdentityIngestedIsTrue = refl
  ; redundantPublicLocatorIngested = true
  ; redundantPublicLocatorIngestedIsTrue = refl
  ; sourceAccessDateIngested = true
  ; sourceAccessDateIngestedIsTrue = refl
  ; experimentArtifactByteChecksumIngested = false
  ; experimentArtifactByteChecksumIngestedIsFalse = refl
  ; publicMirrorsAssertedByteIdentical = false
  ; publicMirrorsAssertedByteIdenticalIsFalse = refl
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
      "The DOI, NIST record/local download, Nature article, JILA public PDF mirror and Glasgow accepted-manuscript deposit provide redundant public location/provenance paths for the Bothwell/Ye publication."
      ∷ "The Glasgow artifact explicitly identifies itself as an author accepted manuscript, so DASHI does not assert byte identity with the Nature version of record or the JILA/NIST artifacts."
      ∷ "No byte checksum is fabricated when the current execution path cannot acquire and hash the selected byte stream."
      ∷ "Publication artifacts remain distinct from the experimental arrays and analysis code, which are tracked through the separate author-acquisition lane."
      ∷ []
  }

canonicalExperimentArtifactIdentityIngested :
  experimentArtifactIdentityIngested canonicalBothwellYe2022PublicArtifactLocator ≡ true
canonicalExperimentArtifactIdentityIngested = refl

canonicalRedundantPublicLocatorIngested :
  redundantPublicLocatorIngested canonicalBothwellYe2022PublicArtifactLocator ≡ true
canonicalRedundantPublicLocatorIngested = refl

canonicalExperimentSourceAccessDateIngested :
  sourceAccessDateIngested canonicalBothwellYe2022PublicArtifactLocator ≡ true
canonicalExperimentSourceAccessDateIngested = refl

canonicalExperimentArtifactChecksumStillOpen :
  experimentArtifactByteChecksumIngested canonicalBothwellYe2022PublicArtifactLocator ≡ false
canonicalExperimentArtifactChecksumStillOpen = refl

------------------------------------------------------------------------
-- Explicit attachment to the existing generic request and original source
-- owner. The attachment is navigational/provenance, not an acceptance token.
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
