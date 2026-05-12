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
-- measurement/covariance numerics.  A declared Z-peak shape callable now runs
-- through a one-parameter covariance-weighted scale fit, but the current shape
-- is not adequate.  The fitted scalar is a dirty calibration diagnostic, not
-- an upstream physical unit authority.

data W4ZPeakCalibrationAnchorWorkerStatus : Set where
  blockedByMissingT21T22ArtifactsAndRunnerInterface :
    W4ZPeakCalibrationAnchorWorkerStatus
  preparedWithT21T22ArtifactsAndPredictionMissing :
    W4ZPeakCalibrationAnchorWorkerStatus
  preparedWithT21T22ArtifactsAndPredictionContractMissing :
    W4ZPeakCalibrationAnchorWorkerStatus
  preparedWithT21T22ArtifactsAndInadequateShapeFit :
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

    dirtyRunnerOutputPath :
      String

    dirtyRunnerOutputSha256 :
      String

    publicIntakeLogPath :
      String

    publicDownloadAccessStatus :
      String

    rejectedPredictionCallable :
      String

    rejectedPredictionCallableStatus :
      String

    exactMissingPredictionContract :
      String

    acceptedShapePredictionCallable :
      String

    shapeFitCalibrationScale :
      String

    shapeFitChi2PerDof :
      String

    shapeFitProjectionDigest :
      String

    shapeFitFirstBinPull :
      String

    shapeFitLastBinPull :
      String

    cssMomentumSpaceDiagnosticStatus :
      String

    cssMomentumSpaceClaimedChi2PerDof :
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
        preparedWithT21T22ArtifactsAndInadequateShapeFit
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
        "7fa002539fef1dc9bd51b22c1d512b4ed7be85417a3afb6f1e9992bbdc3dbdc1"
    ; dirtyRunnerOutputPath =
        "logs/research/w4_z_peak_anchor_dirty_run_20260513.json"
    ; dirtyRunnerOutputSha256 =
        "c8db3b690edcd1b4a792cd772651c5d018d04275d2163007fec7bee6a50a0ada"
    ; publicIntakeLogPath =
        "logs/research/w4_z_peak_t21_t22_public_intake_20260513.json"
    ; publicDownloadAccessStatus =
        "DOI JSON-LD resolves t21 to HEPData record 129900 and t22 to 129901; title and numeric download routes returned HTTP 403 from this environment, so the run used existing checksum-bound local CSVs"
    ; rejectedPredictionCallable =
        "DASHI.Physics.Prediction.sigma_dashi:predict_ratio"
    ; rejectedPredictionCallableStatus =
        "rejected: loaded callable is a t43 ratio predictor and does not declare supportsDirtyZPeakAbsolutePrediction metadata for t21 d sigma/d phistar [pb]"
    ; exactMissingPredictionContract =
        "batch callable list[bin dict] -> list[float] with metadata supportsDirtyZPeakShapePrediction true for uncalibrated shape plus runner-side scalar fit, or supportsDirtyZPeakAbsolutePrediction true for externally calibrated pb predictions"
    ; acceptedShapePredictionCallable =
        "DASHI.Physics.Prediction.sigma_dashi:predict_dirty_z_peak_shape"
    ; shapeFitCalibrationScale =
        "230534508.31238452"
    ; shapeFitChi2PerDof =
        "298.8462841768543"
    ; shapeFitProjectionDigest =
        "7fa002539fef1dc9bd51b22c1d512b4ed7be85417a3afb6f1e9992bbdc3dbdc1"
    ; shapeFitFirstBinPull =
        "-67.35457265472463"
    ; shapeFitLastBinPull =
        "-51.62836040061707"
    ; cssMomentumSpaceDiagnosticStatus =
        "not-present-in-repo-audit: no separate CSS momentum-space/qT dirty Z-peak callable or artifact was found during the W4 shape lane"
    ; cssMomentumSpaceClaimedChi2PerDof =
        "unbound: claimed chi2/dof approximately 65 is not represented by the current local diagnostic; current declared shape chi2/dof is 298.8462841768543"
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
        "prepared-not-closed: dirty-z-peak run parsed t21/t22 digests/schema, accepted the declared Z-peak shape callable, fitted one scalar, and produced chi2/dof 298.8462841768543 in logs/research/w4_z_peak_anchor_dirty_run_20260513.json"
    ; firstMissing =
        ZPeak.missingDirtyZPeakShapeAdequacy
    ; nextProviderAction =
        "supply a materially better Z-peak shape law or an externally calibrated absolute t21 prediction before any comparison law or W4 internal anchor closure is recorded"
    ; nonPromotionBoundary =
        "This diagnostic records a prepared local t21/t22 feasibility check for the W4 Z-peak dirty boundary run"
        ∷ "It does not construct W4SameRecordZPeakRatioCalibrationLaw"
        ∷ "It records a failed dirty shape-fit diagnostic, not an adequate W4 anchor"
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
