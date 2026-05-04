module DASHI.Physics.Closure.HEPDataW3PromotionCandidate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Closure.HEPDataMassKernelCalibrationDiagnostic
open import DASHI.Physics.Closure.HEPDataT43BoundedCleanFreezeRequest

------------------------------------------------------------------------
-- HEP-R51: W3 promotion candidate from bounded t43 clean freeze.
--
-- This receipt records the clean, deterministic t43 projection run after
-- HEP-R50.  It is a W3 promotion candidate, not a final W3 promotion theorem:
-- the projection runner still emits comparisonLawStatus = not-claimed, so a
-- separate comparison-law review must consume the covariance-aware chi2 below.
--
-- Scope is intentionally below-Z t43 only.  The t45 lane remains parked as
-- pdfRequired by HEPDataMassKernelCalibrationDiagnostic.

data W3PromotionCandidateStatus : Set where
  belowZT43CandidatePendingComparisonLawReview :
    W3PromotionCandidateStatus

data ProjectionArtifactReproducibility : Set where
  byteForByteReproducible :
    ProjectionArtifactReproducibility

record HEPDataW3PromotionCandidate : Set where
  field
    boundedRequest :
      HEPDataT43BoundedCleanFreezeRequest

    status :
      W3PromotionCandidateStatus

    freezeCommit :
      String

    projectionArtifact :
      String

    fileSha256 :
      String

    projectionDigest :
      String

    reproducibility :
      ProjectionArtifactReproducibility

    predictionAPI :
      String

    t43DigestStatus :
      Bool

    t44DigestStatus :
      Bool

    t43CovarianceUsed :
      Bool

    cleanChi2 :
      Float

    cleanNBins :
      Float

    cleanChi2PerDof :
      Float

    cleanMeanPredData :
      Float

    cleanResidualMin :
      Float

    cleanResidualMax :
      Float

    chi2Threshold :
      Float

    meanPredDataLowerBound :
      Float

    meanPredDataUpperBound :
      Float

    cleanRunNumericPass :
      Bool

    runnerComparisonLawStatus :
      String

    t45BlockingReceipt :
      HEPDataMassKernelCalibrationDiagnostic

    t45StatusIsPDFRequired :
      HEPDataMassKernelCalibrationDiagnostic.massKernelStatus t45BlockingReceipt
        ≡ pdfRequired

    -- Final W3 promotion still requires a comparison-law receipt that turns
    -- the covariance-aware chi2 into the accepted governance object.
    finalPromotionStillRequiresComparisonLawReceipt :
      ⊤

canonicalHEPDataW3PromotionCandidate :
  HEPDataW3PromotionCandidate
canonicalHEPDataW3PromotionCandidate =
  record
    { boundedRequest = canonicalHEPDataT43BoundedCleanFreezeRequest
    ; status = belowZT43CandidatePendingComparisonLawReview
    ; freezeCommit = "3205d746639568762c9e97adf4a3672c356bd491"
    ; projectionArtifact = "/tmp/t43_clean_freeze.json"
    ; fileSha256 =
        "ffd659e6e2f271d75ec6bf90c5be34cbb9959a8f9d32762c1a2231835fb61eac"
    ; projectionDigest =
        "00f6c23f97f9c0275d90e6ffbf6151b07defcc163708e2d93982d9b7d6866035"
    ; reproducibility = byteForByteReproducible
    ; predictionAPI = "DASHI.Physics.Prediction.sigma_dashi:predict_ratio"
    ; t43DigestStatus = true
    ; t44DigestStatus = true
    ; t43CovarianceUsed = true
    ; cleanChi2 = 38.8173441173
    ; cleanNBins = 18.0
    ; cleanChi2PerDof = 2.1565191176
    ; cleanMeanPredData = 0.9941233097
    ; cleanResidualMin = -0.0019040669
    ; cleanResidualMax = 0.0005400483
    ; chi2Threshold = 4.0
    ; meanPredDataLowerBound = 0.97
    ; meanPredDataUpperBound = 1.03
    ; cleanRunNumericPass = true
    ; runnerComparisonLawStatus = "not-claimed"
    ; t45BlockingReceipt = canonicalHEPDataMassKernelCalibrationDiagnostic
    ; t45StatusIsPDFRequired = refl
    ; finalPromotionStillRequiresComparisonLawReceipt = tt
    }

canonicalHEPDataW3PromotionCandidateNumericPass :
  HEPDataW3PromotionCandidate.cleanRunNumericPass
    canonicalHEPDataW3PromotionCandidate
    ≡ true
canonicalHEPDataW3PromotionCandidateNumericPass = refl
