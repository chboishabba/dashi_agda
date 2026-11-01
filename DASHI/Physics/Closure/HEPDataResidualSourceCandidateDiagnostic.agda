module DASHI.Physics.Closure.HEPDataResidualSourceCandidateDiagnostic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- HEPData residual/deviation source-candidate diagnostic.
--
-- This module records the bounded local source-discovery lane for
-- residual/deviation-like HEPData artifacts already present in this checkout
-- or readable sibling worktrees.  It deliberately stops before promotion:
-- the candidates are path-level artifacts, not accepted empirical receipts.

data ResidualCandidateArtifactClass : Set where
  fitResidualPlot :
    ResidualCandidateArtifactClass
  chi2SummaryTable :
    ResidualCandidateArtifactClass
  chi2PerLabelTable :
    ResidualCandidateArtifactClass
  chi2SweepCurve :
    ResidualCandidateArtifactClass
  lyapunovDiagnosticArtifact :
    ResidualCandidateArtifactClass
  defectMonotonicityReport :
    ResidualCandidateArtifactClass
  seamCertificateScript :
    ResidualCandidateArtifactClass
  covarianceOrPullSearchMiss :
    ResidualCandidateArtifactClass

canonicalResidualCandidateArtifactClasses :
  List ResidualCandidateArtifactClass
canonicalResidualCandidateArtifactClasses =
  fitResidualPlot
  ∷ chi2SummaryTable
  ∷ chi2PerLabelTable
  ∷ chi2SweepCurve
  ∷ lyapunovDiagnosticArtifact
  ∷ defectMonotonicityReport
  ∷ seamCertificateScript
  ∷ covarianceOrPullSearchMiss
  ∷ []

data ResidualCandidateStatus : Set where
  localCandidatesPresentButNoAcceptedReceipt :
    ResidualCandidateStatus

data MissingResidualReceiptField : Set where
  missingExactSelectedObservable :
    MissingResidualReceiptField
  missingRecordTableColumnRowSelection :
    MissingResidualReceiptField
  missingChecksumBoundSchema :
    MissingResidualReceiptField
  missingAcceptedDatasetAuthorityToken :
    MissingResidualReceiptField
  missingUnitAndCalibrationMap :
    MissingResidualReceiptField
  missingComparisonLaw :
    MissingResidualReceiptField
  missingResidualDefinition :
    MissingResidualReceiptField
  missingProviderReceipt :
    MissingResidualReceiptField
  missingGoldenConformanceTest :
    MissingResidualReceiptField

canonicalMissingResidualReceiptFields :
  List MissingResidualReceiptField
canonicalMissingResidualReceiptFields =
  missingExactSelectedObservable
  ∷ missingRecordTableColumnRowSelection
  ∷ missingChecksumBoundSchema
  ∷ missingAcceptedDatasetAuthorityToken
  ∷ missingUnitAndCalibrationMap
  ∷ missingComparisonLaw
  ∷ missingResidualDefinition
  ∷ missingProviderReceipt
  ∷ missingGoldenConformanceTest
  ∷ []

data ResidualPromotionReceipt : Set where

residualPromotionReceiptImpossibleHere :
  ResidualPromotionReceipt →
  ⊥
residualPromotionReceiptImpossibleHere ()

record HEPDataResidualSourceCandidateDiagnostic : Setω where
  field
    selectedObservable :
      String

    candidateStatus :
      ResidualCandidateStatus

    artifactClasses :
      List ResidualCandidateArtifactClass

    artifactClassesAreCanonical :
      artifactClasses ≡ canonicalResidualCandidateArtifactClasses

    candidatePaths :
      List String

    missingReceiptFields :
      List MissingResidualReceiptField

    missingReceiptFieldsAreCanonical :
      missingReceiptFields ≡ canonicalMissingResidualReceiptFields

    noPromotionReceipt :
      ResidualPromotionReceipt → ⊥

    diagnosticBoundary :
      List String

canonicalHEPDataResidualSourceCandidateDiagnostic :
  HEPDataResidualSourceCandidateDiagnostic
canonicalHEPDataResidualSourceCandidateDiagnostic =
  record
    { selectedObservable =
        "none-selected: residual/deviation/anomaly/fit source inventory only"
    ; candidateStatus =
        localCandidatesPresentButNoAcceptedReceipt
    ; artifactClasses =
        canonicalResidualCandidateArtifactClasses
    ; artifactClassesAreCanonical =
        refl
    ; candidatePaths =
        "../dashifine/hepdata_tests_out/pTll_50_76_B_fits_residuals.png"
        ∷ "../dashifine/hepdata_tests_out/phistar_50_76_B_fits_residuals.png"
        ∷ "../dashifine/hepdata_tests_out/pTll_76_106_B_fits_residuals.png"
        ∷ "../dashifine/hepdata_tests_out/pTll_106_170_B_fits_residuals.png"
        ∷ "../dashifine/hepdata_tests_out/pTll_170_350_B_fits_residuals.png"
        ∷ "../dashifine/scale_mdl_fallback_q33_bidirectional_snap_shrink_or_chi2_summary.csv"
        ∷ "../dashifine/scale_mdl_fallback_q33_bidirectional_snap_shrink_or_chi2_per_label.csv"
        ∷ "../dashifine/snap_sweep_q40_min3_chi2_summary.csv"
        ∷ "../dashifine/snap_sweep_q40_min3_chi2_per_label.csv"
        ∷ "../dashifine/snap_sweep_q40_min3_chi2_loss_curve.csv"
        ∷ "../dashifine/snap_sweep_q40_min3_chi2_coverage.csv"
        ∷ "../dashifine/hepdata_lyapunov_test_out/E_beta_minus_logchi2.png"
        ∷ "../dashifine/hepdata_lyapunov_test_out/dashi_idk_out.csv/defect_monotonicity_report.csv"
        ∷ "../dashifine/hepdata_mdl_fejer_out/defect_monotonicity_report.csv"
        ∷ "../dashifine/hepdata_lyapunov_test_out_new/dashi_idk_out/defect_monotonicity_report.csv"
        ∷ "../dashifine/operator_analysis_v2/G_lyapunov.npy"
        ∷ "../dashifine/collapse_signature/G_lyapunov.npy"
        ∷ "../dashifine/26_hepdata_test_lyapunov_against_lhc.py"
        ∷ "../dashifine/26_quadratic_fit.py"
        ∷ "../dashifine/26_quadratic_fit_v2.py"
        ∷ "../dashifine/26_dashi_defect_monotonicity.py"
        ∷ "../dashifine/26_hepdata_seam_certificates.py"
        ∷ "../dashitest/dashifine/hepdata_tests_out/pTll_50_76_B_fits_residuals.png"
        ∷ "../dashitest/dashifine/snap_sweep_q40_min3_chi2_summary.csv"
        ∷ "../dashiQ/temp_dashifine_quantum/hepdata_tests_out/pTll_50_76_B_fits_residuals.png"
        ∷ "../DASHIg/temp_dashiQ/26_hepdata_test_lyapunov_against_lhc.py"
        ∷ []
    ; missingReceiptFields =
        canonicalMissingResidualReceiptFields
    ; missingReceiptFieldsAreCanonical =
        refl
    ; noPromotionReceipt =
        residualPromotionReceiptImpossibleHere
    ; diagnosticBoundary =
        "Search targeted residual, anomaly, chi2, fit, pull, covariance, histogram, defect, lyapunov, and seam names"
        ∷ "Candidate paths are local or readable sibling artifacts only; no network authority was queried"
        ∷ "Fit/residual plots and chi2 tables are not an accepted HEPData receipt without checksum-bound schema and authority"
        ∷ "Lyapunov and defect reports are diagnostic artifacts, not selected physical observables"
        ∷ "No covariance or pull artifact was accepted from this bounded local inventory"
        ∷ "No W3/W4 promotion is performed by this module"
        ∷ []
    }

open HEPDataResidualSourceCandidateDiagnostic public
