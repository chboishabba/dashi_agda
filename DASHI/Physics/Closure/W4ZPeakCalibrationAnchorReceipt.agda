module DASHI.Physics.Closure.W4ZPeakCalibrationAnchorReceipt where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.W4CalibrationRatioZPeakReceiptRequestSurface as ZPeak

------------------------------------------------------------------------
-- W4 Z-peak calibration-anchor worker diagnostic.
--
-- Faraday retrieved the local W4 Z-peak t21/t22 CSVs and bound their digests
-- and parser-visible schema.  The dirty boundary path now parses the real
-- measurement/covariance numerics but still stops at the missing
-- compute_dashi_ratio prediction API.  This file is therefore a non-promoting
-- prepared-anchor diagnostic, not a calibration receipt.

data W4ZPeakCalibrationAnchorWorkerStatus : Set where
  blockedByMissingT21T22ArtifactsAndRunnerInterface :
    W4ZPeakCalibrationAnchorWorkerStatus
  preparedWithT21T22ArtifactsAndPredictionMissing :
    W4ZPeakCalibrationAnchorWorkerStatus

record W4ZPeakCalibrationAnchorMissingArtifactDiagnostic : Setω where
  field
    status :
      W4ZPeakCalibrationAnchorWorkerStatus

    requestSurface :
      ZPeak.W4CalibrationRatioZPeakReceiptRequestSurface

    supportDiagnostic :
      ZPeak.W4ZPeakDirtyBoundaryCheckSupportDiagnostic

    requiredMeasurementLocalPath :
      String

    requiredCovarianceLocalPath :
      String

    measurementSha256 :
      String

    covarianceSha256 :
      String

    measurementRowCount :
      String

    covarianceTotalRowCount :
      String

    covarianceMatrixShape :
      String

    covarianceSymmetryStatus :
      String

    measurementValueColumn :
      String

    firstMeasurementBinValue :
      String

    lastMeasurementBinValue :
      String

    firstTotalCovarianceDiagonal :
      String

    dirtyRunnerProjectionDigest :
      String

    observedLocalCacheFiles :
      List String

    runnerName :
      String

    observedRunnerFlags :
      List String

    absentRunnerFlags :
      List String

    numericRunStatus :
      String

    firstMissing :
      ZPeak.W4CalibrationRatioZPeakMissingRequirement

    nextProviderAction :
      String

    nonPromotionBoundary :
      List String

    noZPeakCalibrationLaw :
      ⊤

    noW4Promotion :
      ⊤

canonicalW4ZPeakCalibrationAnchorMissingArtifactDiagnostic :
  W4ZPeakCalibrationAnchorMissingArtifactDiagnostic
canonicalW4ZPeakCalibrationAnchorMissingArtifactDiagnostic =
  record
    { status =
        preparedWithT21T22ArtifactsAndPredictionMissing
    ; requestSurface =
        ZPeak.canonicalW4CalibrationRatioZPeakReceiptRequestSurface
    ; supportDiagnostic =
        ZPeak.canonicalW4ZPeakDirtyBoundaryCheckSupportDiagnostic
    ; requiredMeasurementLocalPath =
        "scripts/data/hepdata/ins2079374_phistar_mass_76-106_t21.csv"
    ; requiredCovarianceLocalPath =
        "scripts/data/hepdata/ins2079374_Covariance_phistar_mass_76-106_t22.csv"
    ; measurementSha256 =
        "4ece677d0e2640a786351e19d0190454aeb3dc49f7e6fbda4814e3fe88dc3270"
    ; covarianceSha256 =
        "718588d67d3c41195d25a6f01c4ff4bcf2d0d85c193e27ebd22925474a0d9ea7"
    ; measurementRowCount =
        "18"
    ; covarianceTotalRowCount =
        "324"
    ; covarianceMatrixShape =
        "18 x 18"
    ; covarianceSymmetryStatus =
        "symmetric true"
    ; measurementValueColumn =
        "d sigma / d phistar [pb]"
    ; firstMeasurementBinValue =
        "phiStar 0.002, low 0.0, high 0.004, value 6230.5 pb"
    ; lastMeasurementBinValue =
        "phiStar 2.215, low 1.153, high 3.277, value 6.3554 pb"
    ; firstTotalCovarianceDiagonal =
        "t22 Total uncertainty [(pb)^2] covariance[0,0] = 8552.8"
    ; dirtyRunnerProjectionDigest =
        "360e1be033371516e1478f1f19acf90cdcc8b6e0e326f69921b2fea54d87fb67"
    ; observedLocalCacheFiles =
        "scripts/data/hepdata/ins2079374_phistar_mass_76-106_t21.csv"
        ∷ "scripts/data/hepdata/ins2079374_Covariance_phistar_mass_76-106_t22.csv"
        ∷ "scripts/data/hepdata/ins2079374_t21_t22.sha256"
        ∷
        "scripts/data/hepdata/ins2079374_phistar_mass_50-76_over_mass_76-106_t43.csv"
        ∷ "scripts/data/hepdata/ins2079374_Covariance_phistar_mass_50-76_over_mass_76-106_t44.csv"
        ∷ "scripts/data/hepdata/ins2079374_phistar_mass_106-170_over_mass_76-106_t45.csv"
        ∷ "scripts/data/hepdata/ins2079374_Covariance_phistar_mass_106-170_over_mass_76-106_t46.csv"
        ∷ "scripts/data/hepdata/ins2079374_phistar_mass_50-76_t19.csv"
        ∷ "scripts/data/hepdata/ins2079374_Covariance_phistar_mass_50-76_t20.csv"
        ∷ []
    ; runnerName =
        "scripts/run_t43_projection.py"
    ; observedRunnerFlags =
        "--freeze-hash"
        ∷ "--mode"
        ∷ "--data"
        ∷ "--covariance"
        ∷ "--output"
        ∷ "--t43"
        ∷ "--t44"
        ∷ "--prediction-api"
        ∷ []
    ; absentRunnerFlags =
        []
    ; numericRunStatus =
        "prepared-not-closed: dirty-z-peak run parsed t21/t22 digests/schema and exited 42 because compute_dashi_ratio is not wired"
    ; firstMissing =
        ZPeak.missingDirtyZPeakPredictionAPI
    ; nextProviderAction =
        "supply a real compute_dashi_ratio prediction API for the t21 Z-peak measurement carrier before any comparison law or W4 internal anchor closure is recorded"
    ; nonPromotionBoundary =
        "This diagnostic records a prepared local t21/t22 feasibility check for the W4 Z-peak dirty boundary run"
        ∷ "It does not construct W4SameRecordZPeakRatioCalibrationLaw"
        ∷ "It does not construct Candidate256PhysicalCalibrationAuthorityToken"
        ∷ "It does not construct Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "It does not construct physical unit calibration, dimensional preservation, or W4 promotion"
        ∷ []
    ; noZPeakCalibrationLaw =
        tt
    ; noW4Promotion =
        tt
    }

canonicalW4ZPeakCalibrationAnchorNoPromotion :
  W4ZPeakCalibrationAnchorMissingArtifactDiagnostic.noW4Promotion
    canonicalW4ZPeakCalibrationAnchorMissingArtifactDiagnostic
    ≡ tt
canonicalW4ZPeakCalibrationAnchorNoPromotion =
  refl
