module DASHI.Physics.Closure.QuantumClockEmpiricalRedshiftIngestionStatusExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.BothwellYe2022MillimetreRedshiftReceipt as Source
import DASHI.Physics.Closure.BothwellYe2022PublishedGradientPayloadExact as Payload
import DASHI.Physics.Closure.BothwellYe2022RedshiftComparisonExact as Compare
import DASHI.Physics.Closure.QuantumClockEmpiricalRedshiftReceiptRequest as Request
import DASHI.Promotion.SIMetrologyPayloadDependencyDAG as SIDAG

------------------------------------------------------------------------
-- Reconciles the generic fail-closed request with the now-landed concrete
-- Bothwell/Ye source and numeric comparison owners.
--
-- "experiment ingested" is decomposed into levels instead of one ambiguous
-- boolean.  Publication metadata/numbers are present; unpublished raw arrays,
-- checksum and full covariance remain external.  Consequently no generic
-- acceptance token and no terminal SI-metrology promotion is constructed.
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

    publicRawDataIngested : Bool
    publicRawDataIngestedIsFalse : publicRawDataIngested ≡ false
    artifactChecksumIngested : Bool
    artifactChecksumIngestedIsFalse : artifactChecksumIngested ≡ false
    fullCovarianceIngested : Bool
    fullCovarianceIngestedIsFalse : fullCovarianceIngested ≡ false
    analysisCodeIngested : Bool
    analysisCodeIngestedIsFalse : analysisCodeIngested ≡ false

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
  ; publicRawDataIngested = false
  ; publicRawDataIngestedIsFalse = refl
  ; artifactChecksumIngested = false
  ; artifactChecksumIngestedIsFalse = refl
  ; fullCovarianceIngested = false
  ; fullCovarianceIngestedIsFalse = refl
  ; analysisCodeIngested = false
  ; analysisCodeIngestedIsFalse = refl
  ; genericAcceptanceTokenConstructed = false
  ; genericAcceptanceTokenConstructedIsFalse = refl
  ; genericPromotionTokenConstructed = false
  ; genericPromotionTokenConstructedIsFalse = refl
  ; terminalSIMetrologyPromotionAllowed = false
  ; terminalSIMetrologyPromotionAllowedIsFalse = refl
  ; acquisitionResidual =
      "obtain an immutable public or author-supplied artifact byte stream and record its SHA-256"
      ∷ "obtain the experimental arrays underlying the fourteen fitted gradients or an authoritative exported data product"
      ∷ "obtain the analysis code or a reproducible equivalent sufficient to replay the fitted-gradient pipeline"
      ∷ "materialise the full covariance/independence treatment rather than only the published total systematic budget"
      ∷ "construct the generic EmpiricalRedshiftReceiptAcceptanceToken only after those evidence rows are actually satisfied"
      ∷ []
  ; reading =
      "The old generic statement that no experiment was ingested is now refined: a concrete experiment, publication metadata, published numbers and a same-scale comparison are ingested."
      ∷ "What remains un-ingested is the stronger evidence needed by the generic acceptance contract: raw arrays, immutable artifact checksum, replayable code and full covariance/independence evidence."
      ∷ "The published comparison pays empirical consistency at the source-reported summary level but does not open the terminal SI-metrology gate."
      ∷ []
  }

canonicalTerminalSIMetrologyStillClosed :
  terminalSIMetrologyPromotionAllowed canonicalBothwellYe2022IngestionStatus ≡ false
canonicalTerminalSIMetrologyStillClosed = refl

canonicalSIDAGTerminalStillClosed :
  SIDAG.terminalPromotionAllowed SIDAG.canonicalSIMetrologyPayloadDependencyDAG ≡ false
canonicalSIDAGTerminalStillClosed =
  SIDAG.canonicalSIMetrologyTerminalPromotionAllowed
