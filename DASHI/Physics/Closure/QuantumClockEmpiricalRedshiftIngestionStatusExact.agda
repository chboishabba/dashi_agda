module DASHI.Physics.Closure.QuantumClockEmpiricalRedshiftIngestionStatusExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.BothwellYe2022MillimetreRedshiftReceipt as Source
import DASHI.Physics.Closure.BothwellYe2022PublishedGradientPayloadExact as Payload
import DASHI.Physics.Closure.BothwellYe2022RedshiftComparisonExact as Compare
import DASHI.Physics.Closure.BothwellYe2022GeodeticCalibrationExact as Geodetic
import DASHI.Physics.Closure.BothwellYe2022ChronometricGeodesyBridgeExact as Chronometric
import DASHI.Physics.Closure.QuantumClockEmpiricalRedshiftReceiptRequest as Request
import DASHI.Promotion.SIMetrologyPayloadDependencyDAG as SIDAG

------------------------------------------------------------------------
-- Reconciles the generic fail-closed request with the concrete Bothwell/Ye
-- source, published numeric comparison, independently archived geodetic
-- calibration and chronometric-geodesy conversion owners.
--
-- "experiment ingested" is decomposed into evidence levels instead of one
-- ambiguous boolean. Publication metadata/numbers and the cited NOAA
-- calibration are present. NOAA's calibration artifact is checksum-backed;
-- the Nature experiment artifact/raw arrays, analysis code and full covariance
-- remain external. A height-equivalent sensitivity can therefore be derived,
-- but it is not promoted to surveyed elevation accuracy or terminal SI status.
------------------------------------------------------------------------

record EmpiricalRedshiftIngestionStatus : Set where
  field
    experimentName : String
    sourceReceipt : Source.BothwellYe2022ReceiptBoundary
    sourceReceiptIsCanonical : sourceReceipt ≡ Source.canonicalBothwellYe2022ReceiptBoundary
    publishedPayload : Payload.PublishedGradientPayload
    publishedPayloadIsCanonical : publishedPayload ≡ Payload.canonicalPublishedGradientPayload
    comparisonReceipt : Compare.BothwellYe2022ComparisonReceipt
    comparisonReceiptIsCanonical : comparisonReceipt ≡ Compare.canonicalBothwellYe2022ComparisonReceipt
    geodeticCalibrationReceipt : Geodetic.BothwellYe2022GeodeticCalibrationReceipt
    geodeticCalibrationReceiptIsCanonical :
      geodeticCalibrationReceipt ≡ Geodetic.canonicalBothwellYe2022GeodeticCalibrationReceipt
    chronometricGeodesyBridge : Chronometric.BothwellYe2022ChronometricGeodesyBridge
    chronometricGeodesyBridgeIsCanonical :
      chronometricGeodesyBridge ≡ Chronometric.canonicalBothwellYe2022ChronometricGeodesyBridge
    genericRequest : Request.QuantumClockEmpiricalRedshiftReceiptRequest
    genericRequestIsCanonical : genericRequest ≡ Request.canonicalQuantumClockEmpiricalRedshiftReceiptRequest

    experimentIdentified : Bool
    experimentIdentifiedIsTrue : experimentIdentified ≡ true
    publicationMetadataIngested : Bool
    publicationMetadataIngestedIsTrue : publicationMetadataIngested ≡ true
    publishedNumericPayloadIngested : Bool
    publishedNumericPayloadIngestedIsTrue : publishedNumericPayloadIngested ≡ true
    publishedSystematicsSummaryIngested : Bool
    publishedSystematicsSummaryIngestedIsTrue : publishedSystematicsSummaryIngested ≡ true
    sameScaleComparisonConstructed : Bool
    sameScaleComparisonConstructedIsTrue : sameScaleComparisonConstructed ≡ true
    geodeticCalibrationIngested : Bool
    geodeticCalibrationIngestedIsTrue : geodeticCalibrationIngested ≡ true
    geodeticCalibrationChecksumIngested : Bool
    geodeticCalibrationChecksumIngestedIsTrue : geodeticCalibrationChecksumIngested ≡ true
    chronometricGeodesyBridgeConstructed : Bool
    chronometricGeodesyBridgeConstructedIsTrue :
      chronometricGeodesyBridgeConstructed ≡ true
    heightEquivalentScaleConstructed : Bool
    heightEquivalentScaleConstructedIsTrue :
      heightEquivalentScaleConstructed ≡ true

    publicRawDataIngested : Bool
    publicRawDataIngestedIsFalse : publicRawDataIngested ≡ false
    artifactChecksumIngested : Bool
    artifactChecksumIngestedIsFalse : artifactChecksumIngested ≡ false
    experimentPaperArtifactChecksumIngested : Bool
    experimentPaperArtifactChecksumIngestedIsFalse :
      experimentPaperArtifactChecksumIngested ≡ false
    fullCovarianceIngested : Bool
    fullCovarianceIngestedIsFalse : fullCovarianceIngested ≡ false
    analysisCodeIngested : Bool
    analysisCodeIngestedIsFalse : analysisCodeIngested ≡ false
    rawExperimentArraysAcquired : Bool
    rawExperimentArraysAcquiredIsFalse : rawExperimentArraysAcquired ≡ false
    analysisCodeAcquired : Bool
    analysisCodeAcquiredIsFalse : analysisCodeAcquired ≡ false

    chronometricGeodesyPromotionAllowed : Bool
    chronometricGeodesyPromotionAllowedIsFalse :
      chronometricGeodesyPromotionAllowed ≡ false
    genericAcceptanceTokenConstructed : Bool
    genericAcceptanceTokenConstructedIsFalse : genericAcceptanceTokenConstructed ≡ false
    genericPromotionTokenConstructed : Bool
    genericPromotionTokenConstructedIsFalse : genericPromotionTokenConstructed ≡ false
    terminalSIMetrologyPromotionAllowed : Bool
    terminalSIMetrologyPromotionAllowedIsFalse : terminalSIMetrologyPromotionAllowed ≡ false

    acquisitionResidual : List String
    reading : List String

open EmpiricalRedshiftIngestionStatus public

canonicalBothwellYe2022IngestionStatus : EmpiricalRedshiftIngestionStatus
canonicalBothwellYe2022IngestionStatus = record
  { experimentName = "Bothwell et al. 2022 intra-sample 87Sr gravitational-redshift gradient"
  ; sourceReceipt = Source.canonicalBothwellYe2022ReceiptBoundary
  ; sourceReceiptIsCanonical = refl
  ; publishedPayload = Payload.canonicalPublishedGradientPayload
  ; publishedPayloadIsCanonical = refl
  ; comparisonReceipt = Compare.canonicalBothwellYe2022ComparisonReceipt
  ; comparisonReceiptIsCanonical = refl
  ; geodeticCalibrationReceipt = Geodetic.canonicalBothwellYe2022GeodeticCalibrationReceipt
  ; geodeticCalibrationReceiptIsCanonical = refl
  ; chronometricGeodesyBridge = Chronometric.canonicalBothwellYe2022ChronometricGeodesyBridge
  ; chronometricGeodesyBridgeIsCanonical = refl
  ; genericRequest = Request.canonicalQuantumClockEmpiricalRedshiftReceiptRequest
  ; genericRequestIsCanonical = refl
  ; experimentIdentified = true
  ; experimentIdentifiedIsTrue = refl
  ; publicationMetadataIngested = true
  ; publicationMetadataIngestedIsTrue = refl
  ; publishedNumericPayloadIngested = true
  ; publishedNumericPayloadIngestedIsTrue = refl
  ; publishedSystematicsSummaryIngested = true
  ; publishedSystematicsSummaryIngestedIsTrue = refl
  ; sameScaleComparisonConstructed = true
  ; sameScaleComparisonConstructedIsTrue = refl
  ; geodeticCalibrationIngested = true
  ; geodeticCalibrationIngestedIsTrue = refl
  ; geodeticCalibrationChecksumIngested = true
  ; geodeticCalibrationChecksumIngestedIsTrue = refl
  ; chronometricGeodesyBridgeConstructed = true
  ; chronometricGeodesyBridgeConstructedIsTrue = refl
  ; heightEquivalentScaleConstructed = true
  ; heightEquivalentScaleConstructedIsTrue = refl
  ; publicRawDataIngested = false
  ; publicRawDataIngestedIsFalse = refl
  ; artifactChecksumIngested = false
  ; artifactChecksumIngestedIsFalse = refl
  ; experimentPaperArtifactChecksumIngested = false
  ; experimentPaperArtifactChecksumIngestedIsFalse = refl
  ; fullCovarianceIngested = false
  ; fullCovarianceIngestedIsFalse = refl
  ; analysisCodeIngested = false
  ; analysisCodeIngestedIsFalse = refl
  ; rawExperimentArraysAcquired = false
  ; rawExperimentArraysAcquiredIsFalse = refl
  ; analysisCodeAcquired = false
  ; analysisCodeAcquiredIsFalse = refl
  ; chronometricGeodesyPromotionAllowed = false
  ; chronometricGeodesyPromotionAllowedIsFalse = refl
  ; genericAcceptanceTokenConstructed = false
  ; genericAcceptanceTokenConstructedIsFalse = refl
  ; genericPromotionTokenConstructed = false
  ; genericPromotionTokenConstructedIsFalse = refl
  ; terminalSIMetrologyPromotionAllowed = false
  ; terminalSIMetrologyPromotionAllowedIsFalse = refl
  ; acquisitionResidual =
      "pin/checksum the exact experiment publication or author-supplied experiment artifact bytes used for terminal ingestion"
      ∷ "obtain the experimental arrays underlying the fourteen fitted gradients or an authoritative exported data product"
      ∷ "obtain the analysis code or a reproducible equivalent sufficient to replay the fitted-gradient pipeline"
      ∷ "materialise the full covariance/independence treatment rather than only the published total systematic budget"
      ∷ "for geodetic-accuracy promotion, also pay survey transfer/geopotential modelling rather than identifying a height-equivalent sensitivity with elevation accuracy"
      ∷ "construct the generic EmpiricalRedshiftReceiptAcceptanceToken only after those experiment-evidence rows are actually satisfied"
      ∷ []
  ; reading =
      "A concrete experiment, publication metadata, published numbers, source-reported systematics and a same-scale gh/c^2 comparison are ingested."
      ∷ "The geodetic calibration is independently source-closed at the public-artifact level: NOAA NOS NGS 77 is DOI-pinned, checksum-backed, and its JILA S1B60H gravity value rounds to the paper's 9.796 m s^-2 input."
      ∷ "The clock uncertainty, surveyed gravity and exact SI metre/c route now produce a 69-to-70 micrometre local height-equivalent scale without promoting that scale to surveyed elevation accuracy."
      ∷ "The NOAA checksum closes the calibration artifact only; it does not manufacture a checksum for the experiment paper, raw experimental arrays, analysis code or full covariance evidence."
      ∷ "The published comparison pays empirical consistency at the source-reported summary level but neither chronometric-geodesy nor terminal SI-metrology promotion is opened."
      ∷ []
  }

canonicalTerminalSIMetrologyStillClosed :
  terminalSIMetrologyPromotionAllowed canonicalBothwellYe2022IngestionStatus ≡ false
canonicalTerminalSIMetrologyStillClosed = refl

canonicalGeodeticCalibrationIngested :
  geodeticCalibrationIngested canonicalBothwellYe2022IngestionStatus ≡ true
canonicalGeodeticCalibrationIngested = refl

canonicalGeodeticCalibrationChecksumIngested :
  geodeticCalibrationChecksumIngested canonicalBothwellYe2022IngestionStatus ≡ true
canonicalGeodeticCalibrationChecksumIngested = refl

canonicalChronometricGeodesyBridgeConstructed :
  chronometricGeodesyBridgeConstructed canonicalBothwellYe2022IngestionStatus ≡ true
canonicalChronometricGeodesyBridgeConstructed = refl

canonicalChronometricGeodesyPromotionStillClosed :
  chronometricGeodesyPromotionAllowed canonicalBothwellYe2022IngestionStatus ≡ false
canonicalChronometricGeodesyPromotionStillClosed = refl

canonicalSIDAGTerminalStillClosed :
  SIDAG.terminalPromotionAllowed SIDAG.canonicalSIMetrologyPayloadDependencyDAG ≡ false
canonicalSIDAGTerminalStillClosed =
  SIDAG.canonicalSIMetrologyTerminalPromotionAllowed
