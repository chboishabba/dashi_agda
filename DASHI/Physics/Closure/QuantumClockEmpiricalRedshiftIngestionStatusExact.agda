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
import DASHI.Physics.Closure.BothwellYe2022AntigravityMetricClockBridgeExact as AntiClock
import DASHI.Physics.Closure.BothwellYe2022PublicArtifactLocatorExact as Artifact
import DASHI.Physics.Closure.BothwellYe2022ExternalAcquisitionMaxCut as Acquisition
import DASHI.Physics.Closure.QuantumClockEmpiricalRedshiftReceiptRequest as Request
import DASHI.Promotion.SIMetrologyPayloadDependencyDAG as SIDAG

------------------------------------------------------------------------
-- Staged empirical-redshift ingestion status.
--
-- The publication identity/access-date, published summary numbers, geodetic
-- calibration and a same-scale theory/observation comparison are present.
-- The NOAA calibration artifact is checksum-backed. The experiment paper has
-- a stable NIST public locator and explicit access date, but its byte digest is
-- still not materialised here. Raw arrays, analysis code and full covariance
-- remain external. The remaining external evidence is now also represented by
-- an explicit author-acquisition packet; constructing that packet is not the
-- same as sending it or receiving evidence.
--
-- The standard clock result is also registered as a metric-clock reference for
-- the antigravity proof-search lane. That cross-pollination is deliberately a
-- reference/negative-control surface only: no exotic intervention, engineered
-- metric response, negative-G inference, mechanism validation or promotion is
-- thereby created.
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
    antigravityMetricClockBridge : AntiClock.BothwellYe2022AntigravityMetricClockBridge
    antigravityMetricClockBridgeIsCanonical :
      antigravityMetricClockBridge ≡ AntiClock.canonicalBothwellYe2022AntigravityMetricClockBridge
    experimentArtifactLocator : Artifact.PublicExperimentArtifactLocator
    experimentArtifactLocatorIsCanonical :
      experimentArtifactLocator ≡ Artifact.canonicalBothwellYe2022PublicArtifactLocator
    externalAcquisition : Acquisition.BothwellYe2022ExternalAcquisitionMaxCut
    externalAcquisitionIsCanonical :
      externalAcquisition ≡ Acquisition.canonicalBothwellYe2022ExternalAcquisitionMaxCut
    genericRequest : Request.QuantumClockEmpiricalRedshiftReceiptRequest
    genericRequestIsCanonical : genericRequest ≡ Request.canonicalQuantumClockEmpiricalRedshiftReceiptRequest

    experimentIdentified : Bool
    experimentIdentifiedIsTrue : experimentIdentified ≡ true
    publicationMetadataIngested : Bool
    publicationMetadataIngestedIsTrue : publicationMetadataIngested ≡ true
    experimentArtifactIdentityIngested : Bool
    experimentArtifactIdentityIngestedIsTrue : experimentArtifactIdentityIngested ≡ true
    experimentSourceAccessDateIngested : Bool
    experimentSourceAccessDateIngestedIsTrue : experimentSourceAccessDateIngested ≡ true
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
    chronometricGeodesyBridgeConstructedIsTrue : chronometricGeodesyBridgeConstructed ≡ true
    heightEquivalentScaleConstructed : Bool
    heightEquivalentScaleConstructedIsTrue : heightEquivalentScaleConstructed ≡ true
    antigravityMetricClockBridgeConstructed : Bool
    antigravityMetricClockBridgeConstructedIsTrue :
      antigravityMetricClockBridgeConstructed ≡ true
    externalAcquisitionPacketConstructed : Bool
    externalAcquisitionPacketConstructedIsTrue :
      externalAcquisitionPacketConstructed ≡ true
    externalAuthorRequestSent : Bool
    externalAuthorRequestSentIsFalse : externalAuthorRequestSent ≡ false

    publicRawDataIngested : Bool
    publicRawDataIngestedIsFalse : publicRawDataIngested ≡ false
    artifactChecksumIngested : Bool
    artifactChecksumIngestedIsFalse : artifactChecksumIngested ≡ false
    experimentPaperArtifactChecksumIngested : Bool
    experimentPaperArtifactChecksumIngestedIsFalse : experimentPaperArtifactChecksumIngested ≡ false
    fullCovarianceIngested : Bool
    fullCovarianceIngestedIsFalse : fullCovarianceIngested ≡ false
    analysisCodeIngested : Bool
    analysisCodeIngestedIsFalse : analysisCodeIngested ≡ false
    rawExperimentArraysAcquired : Bool
    rawExperimentArraysAcquiredIsFalse : rawExperimentArraysAcquired ≡ false
    analysisCodeAcquired : Bool
    analysisCodeAcquiredIsFalse : analysisCodeAcquired ≡ false

    chronometricGeodesyPromotionAllowed : Bool
    chronometricGeodesyPromotionAllowedIsFalse : chronometricGeodesyPromotionAllowed ≡ false
    antigravityMetricClockPromotionAllowed : Bool
    antigravityMetricClockPromotionAllowedIsFalse :
      antigravityMetricClockPromotionAllowed ≡ false
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
  ; antigravityMetricClockBridge = AntiClock.canonicalBothwellYe2022AntigravityMetricClockBridge
  ; antigravityMetricClockBridgeIsCanonical = refl
  ; experimentArtifactLocator = Artifact.canonicalBothwellYe2022PublicArtifactLocator
  ; experimentArtifactLocatorIsCanonical = refl
  ; externalAcquisition = Acquisition.canonicalBothwellYe2022ExternalAcquisitionMaxCut
  ; externalAcquisitionIsCanonical = refl
  ; genericRequest = Request.canonicalQuantumClockEmpiricalRedshiftReceiptRequest
  ; genericRequestIsCanonical = refl
  ; experimentIdentified = true
  ; experimentIdentifiedIsTrue = refl
  ; publicationMetadataIngested = true
  ; publicationMetadataIngestedIsTrue = refl
  ; experimentArtifactIdentityIngested = true
  ; experimentArtifactIdentityIngestedIsTrue = refl
  ; experimentSourceAccessDateIngested = true
  ; experimentSourceAccessDateIngestedIsTrue = refl
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
  ; antigravityMetricClockBridgeConstructed = true
  ; antigravityMetricClockBridgeConstructedIsTrue = refl
  ; externalAcquisitionPacketConstructed = true
  ; externalAcquisitionPacketConstructedIsTrue = refl
  ; externalAuthorRequestSent = false
  ; externalAuthorRequestSentIsFalse = refl
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
  ; antigravityMetricClockPromotionAllowed = false
  ; antigravityMetricClockPromotionAllowedIsFalse = refl
  ; genericAcceptanceTokenConstructed = false
  ; genericAcceptanceTokenConstructedIsFalse = refl
  ; genericPromotionTokenConstructed = false
  ; genericPromotionTokenConstructedIsFalse = refl
  ; terminalSIMetrologyPromotionAllowed = false
  ; terminalSIMetrologyPromotionAllowedIsFalse = refl
  ; acquisitionResidual =
      "send the typed evidence request to a listed corresponding author; request construction alone is not evidence acquisition"
      ∷ "materialise and checksum the exact experiment/data artifact byte stream selected for terminal ingestion"
      ∷ "obtain the experimental arrays underlying the fourteen fitted gradients or an authoritative exported data product"
      ∷ "obtain the analysis code and exact revision/environment sufficient to replay the fitted-gradient pipeline"
      ∷ "materialise the full covariance/independence treatment rather than only the published total systematic budget"
      ∷ "for geodetic-accuracy promotion, also pay survey transfer/geopotential modelling rather than identifying a height-equivalent sensitivity with elevation accuracy"
      ∷ "for exotic-gravity use, acquire a same-object engineered intervention and the claim-specific metricClockDiscriminator adequacy witness; the ordinary-gravity clock reference alone is only a control/reference surface"
      ∷ "construct the generic EmpiricalRedshiftReceiptAcceptanceToken only after those experiment-evidence rows are actually satisfied"
      ∷ []
  ; reading =
      "The experiment publication is identified by DOI plus a stable NIST record/local-PDF locator with explicit access date; byte checksum remains separate."
      ∷ "Published numbers, source-reported systematics and a same-scale gh/c^2 comparison are ingested."
      ∷ "The geodetic calibration is independently source-closed at the public-artifact level: NOAA NOS NGS 77 is DOI-pinned, checksum-backed, and its JILA S1B60H gravity value rounds to the paper's 9.796 m s^-2 input."
      ∷ "The clock uncertainty, surveyed gravity and exact SI metre/c route produce a 69-to-70 micrometre local height-equivalent scale without promoting that scale to surveyed elevation accuracy."
      ∷ "The same clock result now pays a standard-gravity metric/clock reference coordinate for antigravity proof search, but no exotic intervention or antigravity consumer adequacy is inferred from it."
      ∷ "The remaining author-supplied evidence is represented by a typed request packet that separates requested bytes/data/code from repository-owned checksum/replay/consumer-ingestion work."
      ∷ "Constructing that packet does not mean it has been sent and does not manufacture raw experimental arrays, analysis code, covariance evidence or a generic acceptance token."
      ∷ []
  }

canonicalTerminalSIMetrologyStillClosed : terminalSIMetrologyPromotionAllowed canonicalBothwellYe2022IngestionStatus ≡ false
canonicalTerminalSIMetrologyStillClosed = refl

canonicalExperimentArtifactIdentityIngested : experimentArtifactIdentityIngested canonicalBothwellYe2022IngestionStatus ≡ true
canonicalExperimentArtifactIdentityIngested = refl

canonicalExperimentSourceAccessDateIngested : experimentSourceAccessDateIngested canonicalBothwellYe2022IngestionStatus ≡ true
canonicalExperimentSourceAccessDateIngested = refl

canonicalGeodeticCalibrationIngested : geodeticCalibrationIngested canonicalBothwellYe2022IngestionStatus ≡ true
canonicalGeodeticCalibrationIngested = refl

canonicalGeodeticCalibrationChecksumIngested : geodeticCalibrationChecksumIngested canonicalBothwellYe2022IngestionStatus ≡ true
canonicalGeodeticCalibrationChecksumIngested = refl

canonicalChronometricGeodesyBridgeConstructed : chronometricGeodesyBridgeConstructed canonicalBothwellYe2022IngestionStatus ≡ true
canonicalChronometricGeodesyBridgeConstructed = refl

canonicalAntigravityMetricClockBridgeConstructed : antigravityMetricClockBridgeConstructed canonicalBothwellYe2022IngestionStatus ≡ true
canonicalAntigravityMetricClockBridgeConstructed = refl

canonicalAntigravityMetricClockPromotionStillClosed : antigravityMetricClockPromotionAllowed canonicalBothwellYe2022IngestionStatus ≡ false
canonicalAntigravityMetricClockPromotionStillClosed = refl

canonicalExternalAcquisitionPacketConstructed : externalAcquisitionPacketConstructed canonicalBothwellYe2022IngestionStatus ≡ true
canonicalExternalAcquisitionPacketConstructed = refl

canonicalExternalAuthorRequestNotSent : externalAuthorRequestSent canonicalBothwellYe2022IngestionStatus ≡ false
canonicalExternalAuthorRequestNotSent = refl

canonicalChronometricGeodesyPromotionStillClosed : chronometricGeodesyPromotionAllowed canonicalBothwellYe2022IngestionStatus ≡ false
canonicalChronometricGeodesyPromotionStillClosed = refl

canonicalSIDAGTerminalStillClosed : SIDAG.terminalPromotionAllowed SIDAG.canonicalSIMetrologyPayloadDependencyDAG ≡ false
canonicalSIDAGTerminalStillClosed = SIDAG.canonicalSIMetrologyTerminalPromotionAllowed
