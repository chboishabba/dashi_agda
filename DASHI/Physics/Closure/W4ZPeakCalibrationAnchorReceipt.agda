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
-- Faraday checked the local W4 Z-peak path without editing the projection
-- runner.  The dirty boundary run cannot be produced from the current local
-- state: the same-record t21/t22 artifacts are absent and the runner is still
-- the digest-bound t43/t44 interface.  This file is therefore a non-promoting
-- missing-artifact diagnostic, not a calibration receipt.

data W4ZPeakCalibrationAnchorWorkerStatus : Set where
  blockedByMissingT21T22ArtifactsAndRunnerInterface :
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
        blockedByMissingT21T22ArtifactsAndRunnerInterface
    ; requestSurface =
        ZPeak.canonicalW4CalibrationRatioZPeakReceiptRequestSurface
    ; supportDiagnostic =
        ZPeak.canonicalW4ZPeakDirtyBoundaryCheckSupportDiagnostic
    ; requiredMeasurementLocalPath =
        "scripts/data/hepdata/ins2079374_phistar_mass_76-106_t21.csv"
    ; requiredCovarianceLocalPath =
        "scripts/data/hepdata/ins2079374_Covariance_phistar_mass_76-106_t22.csv"
    ; observedLocalCacheFiles =
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
        ∷ "--output"
        ∷ "--t43"
        ∷ "--t44"
        ∷ "--prediction-api"
        ∷ []
    ; absentRunnerFlags =
        "--mode"
        ∷ "--data"
        ∷ "--covariance"
        ∷ []
    ; numericRunStatus =
        "not-run: same-record t21/t22 artifacts are absent locally and current runner is t43/t44-specific"
    ; firstMissing =
        ZPeak.missingSameRecordT21T22ArtifactReceipt
    ; nextProviderAction =
        "supply checksum-bound t21 measurement and t22 covariance artifacts, then generalize the runner or add a Z-peak-specific runner before any dirty boundary numeric anchor is recorded"
    ; nonPromotionBoundary =
        "This diagnostic records a failed local feasibility check for the W4 Z-peak dirty boundary run"
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
