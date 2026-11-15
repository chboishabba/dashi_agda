module DASHI.Physics.Closure.BothwellYe2022GeodeticCalibrationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (_+_; _≤ᵇ_)

import DASHI.Physics.Closure.BothwellYe2022PublishedGradientPayloadExact as Payload

------------------------------------------------------------------------
-- Geodetic calibration provenance for the Bothwell/Ye 2022 redshift result.
--
-- Bothwell et al. explicitly cite Derek van Westrum, NOAA Technical
-- Memorandum NOS NGS 77 (2019), for the local gravitational acceleration
-- used in the redshift prediction.  NOAA's institutional repository exposes
-- a stable DOI, public-domain archival PDF and SHA-512 checksum.
--
-- The survey's reduced gravity value at the Ye-lab benchmark JILA S1B60H is
--
--   979,607,868.4 microGal = 9.796078684 m s^-2.
--
-- The Nature paper reports the value rounded to four significant digits:
--
--   a = -9.796 m s^-2.
--
-- Using nanometres per second squared makes the rounding relation an exact
-- natural-number statement:
--
--   9.796078684 m s^-2 = 9,796,078,684 nm s^-2
--   9.796       m s^-2 = 9,796,000,000 nm s^-2
--   residual                  =    78,684 nm s^-2
--
-- which is strictly below half of the 0.001 m s^-2 rounding step
-- (500,000 nm s^-2).
--
-- A later NOAA 2025 survey supersedes NOS NGS 77 as current geodetic
-- documentation.  It is retained here as provenance evolution only; it does
-- not retroactively rewrite the number actually used by the 2022 paper.
------------------------------------------------------------------------

record GeodeticArtifact : Set where
  field
    title : String
    author : String
    corporateAuthor : String
    year : String
    series : String
    doi : String
    archiveUri : String
    checksumAlgorithm : String
    archiveChecksum : String
    publicDomain : Bool
    publicDomainIsTrue : publicDomain ≡ true

open GeodeticArtifact public

noaaNOSNGS77Artifact : GeodeticArtifact
noaaNOSNGS77Artifact = record
  { title = "Geodetic Survey of NIST and JILA Clock Laboratories, Boulder, Colorado"
  ; author = "Derek van Westrum"
  ; corporateAuthor = "NOAA National Geodetic Survey"
  ; year = "2019"
  ; series = "NOAA Technical Memorandum NOS NGS 77"
  ; doi = "10.25923/zm69-rt94"
  ; archiveUri = "https://repository.library.noaa.gov/view/noaa/52062"
  ; checksumAlgorithm = "SHA-512"
  ; archiveChecksum = "12022b3b7a632a71d966bed565bf61a7cc1abc2411d6d95702bc3116cdf13fd8069ff3a108ba0667135ff59607ead54e232f9ad75af51e8c222beeef76354454"
  ; publicDomain = true
  ; publicDomainIsTrue = refl
  }

noaaNOSNGS99Artifact : GeodeticArtifact
noaaNOSNGS99Artifact = record
  { title = "Geodetic Survey of NIST, JILA, University of Colorado, and Table Mountain Laboratories"
  ; author = "Derek van Westrum and Kevin Ahlgren"
  ; corporateAuthor = "NOAA National Geodetic Survey"
  ; year = "2025"
  ; series = "NOAA Technical Memorandum NOS NGS 99"
  ; doi = "10.25923/8s2t-kh22"
  ; archiveUri = "https://repository.library.noaa.gov/view/noaa/70289"
  ; checksumAlgorithm = "SHA-512"
  ; archiveChecksum = "f907622c980f8d7dedf3b2785c7ecfe0841e861f2197285e087545d852be2951f4505e96bfa1571d6eb5363569105336cb74bfcb8d1541512d921e251ea27a48"
  ; publicDomain = true
  ; publicDomainIsTrue = refl
  }

sourceBenchmark : String
sourceBenchmark = "JILA S1B60H"

sourceReducedGravityText : String
sourceReducedGravityText = "979607868.4 microGal"

-- One tenth of a microGal is exactly one nm s^-2 because
-- 1 microGal = 1e-8 m s^-2 = 10 nm s^-2.
sourceGravityNanoMetresPerSecondSquared : Nat
sourceGravityNanoMetresPerSecondSquared = 9796078684

paperRoundedGravityNanoMetresPerSecondSquared : Nat
paperRoundedGravityNanoMetresPerSecondSquared = 9796000000

roundingResidualNanoMetresPerSecondSquared : Nat
roundingResidualNanoMetresPerSecondSquared = 78684

canonicalGeodeticRoundingResidualIdentity :
  sourceGravityNanoMetresPerSecondSquared ≡
  paperRoundedGravityNanoMetresPerSecondSquared +
  roundingResidualNanoMetresPerSecondSquared
canonicalGeodeticRoundingResidualIdentity = refl

halfMilliMetrePerSecondSquaredInNanoUnits : Nat
halfMilliMetrePerSecondSquaredInNanoUnits = 500000

roundingResidualWithinHalfMilliMetrePerSecondSquared : Bool
roundingResidualWithinHalfMilliMetrePerSecondSquared =
  roundingResidualNanoMetresPerSecondSquared ≤ᵇ
  halfMilliMetrePerSecondSquaredInNanoUnits

canonicalRoundingResidualWithinHalfMilliMetrePerSecondSquared :
  roundingResidualWithinHalfMilliMetrePerSecondSquared ≡ true
canonicalRoundingResidualWithinHalfMilliMetrePerSecondSquared = refl

record BothwellYe2022GeodeticCalibrationReceipt : Set where
  field
    contemporaneousSurvey : GeodeticArtifact
    contemporaneousSurveyIsCanonical : contemporaneousSurvey ≡ noaaNOSNGS77Artifact

    laterSurvey : GeodeticArtifact
    laterSurveyIsCanonical : laterSurvey ≡ noaaNOSNGS99Artifact

    experimentPayload : Payload.PublishedGradientPayload
    experimentPayloadIsCanonical :
      experimentPayload ≡ Payload.canonicalPublishedGradientPayload

    benchmark : String
    measuredGravity : String

    geodeticArtifactChecksumRecorded : Bool
    geodeticArtifactChecksumRecordedIsTrue :
      geodeticArtifactChecksumRecorded ≡ true

    paperUsesRoundedGeodeticValue : Bool
    paperUsesRoundedGeodeticValueIsTrue :
      paperUsesRoundedGeodeticValue ≡ true

    laterSurveySupersedesNOSNGS77 : Bool
    laterSurveySupersedesNOSNGS77IsTrue :
      laterSurveySupersedesNOSNGS77 ≡ true

    laterSurveyRewritesPublished2022Calibration : Bool
    laterSurveyRewritesPublished2022CalibrationIsFalse :
      laterSurveyRewritesPublished2022Calibration ≡ false

    experimentPaperArtifactChecksumRecorded : Bool
    experimentPaperArtifactChecksumRecordedIsFalse :
      experimentPaperArtifactChecksumRecorded ≡ false

    rawExperimentArraysAcquired : Bool
    rawExperimentArraysAcquiredIsFalse : rawExperimentArraysAcquired ≡ false

    analysisCodeAcquired : Bool
    analysisCodeAcquiredIsFalse : analysisCodeAcquired ≡ false

    reading : List String

open BothwellYe2022GeodeticCalibrationReceipt public

canonicalBothwellYe2022GeodeticCalibrationReceipt :
  BothwellYe2022GeodeticCalibrationReceipt
canonicalBothwellYe2022GeodeticCalibrationReceipt = record
  { contemporaneousSurvey = noaaNOSNGS77Artifact
  ; contemporaneousSurveyIsCanonical = refl
  ; laterSurvey = noaaNOSNGS99Artifact
  ; laterSurveyIsCanonical = refl
  ; experimentPayload = Payload.canonicalPublishedGradientPayload
  ; experimentPayloadIsCanonical = refl
  ; benchmark = sourceBenchmark
  ; measuredGravity = sourceReducedGravityText
  ; geodeticArtifactChecksumRecorded = true
  ; geodeticArtifactChecksumRecordedIsTrue = refl
  ; paperUsesRoundedGeodeticValue = true
  ; paperUsesRoundedGeodeticValueIsTrue = refl
  ; laterSurveySupersedesNOSNGS77 = true
  ; laterSurveySupersedesNOSNGS77IsTrue = refl
  ; laterSurveyRewritesPublished2022Calibration = false
  ; laterSurveyRewritesPublished2022CalibrationIsFalse = refl
  ; experimentPaperArtifactChecksumRecorded = false
  ; experimentPaperArtifactChecksumRecordedIsFalse = refl
  ; rawExperimentArraysAcquired = false
  ; rawExperimentArraysAcquiredIsFalse = refl
  ; analysisCodeAcquired = false
  ; analysisCodeAcquiredIsFalse = refl
  ; reading =
      "NOAA NOS NGS 77 is the independently archived geodetic source cited by Bothwell et al. for the local laboratory acceleration."
      ∷ "Its JILA S1B60H reduced gravity value is 979607868.4 microGal, exactly 9.796078684 m s^-2."
      ∷ "The Nature paper's 9.796 m s^-2 input is the expected four-significant-digit rounding; the exact integer residual is below half of the 0.001 m s^-2 rounding step."
      ∷ "NOAA's archival SHA-512 closes checksum provenance for the geodetic calibration artifact, not for the Nature experiment PDF or unpublished experimental arrays."
      ∷ "The 2025 NOAA NOS NGS 99 survey supersedes the earlier geodetic report as current documentation but does not rewrite the value historically used in the 2022 analysis."
      ∷ []
  }

canonicalGeodeticArtifactChecksumPaid :
  geodeticArtifactChecksumRecorded
    canonicalBothwellYe2022GeodeticCalibrationReceipt
  ≡ true
canonicalGeodeticArtifactChecksumPaid = refl

canonicalExperimentRawArraysRemainExternal :
  rawExperimentArraysAcquired
    canonicalBothwellYe2022GeodeticCalibrationReceipt
  ≡ false
canonicalExperimentRawArraysRemainExternal = refl
