module DASHI.Physics.Optics.BerkeleyDiffuserCamRealConditioningExecutionExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Optics.BerkeleyDiffuserCamPublicCalibrationExact as Calibration

------------------------------------------------------------------------
-- REAL WALLER DIFFUSERCAM CONDITIONING EXECUTION RECEIPT — 2026-10-16
--
-- User-supplied example_psfs.mat was executed locally against the branch's
-- exact source-H audit. Before execution, artifact identity was independently
-- verified by both byte count and Git blob SHA-1:
--
--   bytes  = 10,823,885
--   blob   = db59065bdaf44fe771a6d3fbe22ae3c703527b5f
--   sha256 = fdbc8b2c7a8753f146e1b270a3f0ae2d0f70cb2c4ff49aef4a926670c0f7c906
--
-- The MAT contains psf : 270 x 320 x 44.  The executed audit mirrors the
-- pinned Waller MATLAB preprocessing and selected source-H construction.
--
-- Promotion boundary:
--   * depth SVD/Gram numerical receipt: paid;
--   * translated selected-column numerical receipt: paid;
--   * finite radius-1 k=1 restricted lower-bound/kappa receipt: paid;
--   * all-resolution RIP / k>=2 sparse guarantee: NOT paid;
--   * matched-photon comparison: NOT paid.
------------------------------------------------------------------------

realConditioningReceiptPath : String
realConditioningReceiptPath = "receipts/optics/waller_diffusercam_real_conditioning_receipt.json"

realConditioningReceiptGitBlobSHA : String
realConditioningReceiptGitBlobSHA = "6a6af1ee870e5584b590c3d94d054e186f0aec63"

realClaimScaleReceiptPath : String
realClaimScaleReceiptPath = "receipts/optics/waller_diffusercam_real_claim_scale_receipt.json"

realClaimScaleReceiptGitBlobSHA : String
realClaimScaleReceiptGitBlobSHA = "96839e591b73250c6dad04bb81f82e9c9dc57e4e"

verifiedArtifactGitBlobSHA : String
verifiedArtifactGitBlobSHA = "db59065bdaf44fe771a6d3fbe22ae3c703527b5f"

verifiedArtifactSHA256 : String
verifiedArtifactSHA256 = "fdbc8b2c7a8753f146e1b270a3f0ae2d0f70cb2c4ff49aef4a926670c0f7c906"

verifiedArtifactBytes : Nat
verifiedArtifactBytes = 10823885

psfNy : Nat
psfNy = 270
psfNx : Nat
psfNx = 320
psfNz : Nat
psfNz = 44

numericalRank : Nat
numericalRank = 44

selectedColumnCount : Nat
selectedColumnCount = 396

selectedLateralRadius : Nat
selectedLateralRadius = 1

selectedLateralStep : Nat
selectedLateralStep = 1

maxSceneSparsityPositiveBound : Nat
maxSceneSparsityPositiveBound = 1

largestPlannerSafeRadius5GiB : Nat
largestPlannerSafeRadius5GiB = 3

firstUnsafePlannerRadius5GiB : Nat
firstUnsafePlannerRadius5GiB = 4

depthMatrixConditionNumber : String
depthMatrixConditionNumber = "255.26888545359984"

translatedColumnMutualCoherence : String
translatedColumnMutualCoherence = "0.9774115205968726"

minimumTranslatedColumnNorm : String
minimumTranslatedColumnNorm = "0.08673434320488643"

k1NormalizedGramLowerBound : String
k1NormalizedGramLowerBound = "0.02258847940312736"

k1SensorGainLowerBound : String
k1SensorGainLowerBound = "0.013035707057972764"

k1RestrictedKappaUpperBound : String
k1RestrictedKappaUpperBound = "76.71237130082564"

fftVsRollMaxAbsError : String
fftVsRollMaxAbsError = "5.204170427930421e-18"

realPSFArtifactBytesVerified : Bool
realPSFArtifactBytesVerified = true

realPSFArtifactIdentityVerified : Bool
realPSFArtifactIdentityVerified = true

depthOnlyNumericalReceiptCaptured : Bool
depthOnlyNumericalReceiptCaptured = true

translatedColumnNumericalReceiptCaptured : Bool
translatedColumnNumericalReceiptCaptured = true

finiteSelectedFamilyRestrictedKappaPaid : Bool
finiteSelectedFamilyRestrictedKappaPaid = true

realClaimScalePlannerReceiptCaptured : Bool
realClaimScalePlannerReceiptCaptured = true

allResolutionCameraRIPPaid : Bool
allResolutionCameraRIPPaid = false

matchedPhotonComparisonPaid : Bool
matchedPhotonComparisonPaid = false

record BerkeleyDiffuserCamRealConditioningExecutionReceipt : Set where
  field
    calibrationArtifactPinned : Bool
    bytesVerified : Bool
    identityVerified : Bool
    depthReceipt : Bool
    translatedReceipt : Bool
    finiteRestrictedKappa : Bool
    plannerReceipt : Bool
    allResolutionRIP : Bool
    matchedPhoton : Bool

open BerkeleyDiffuserCamRealConditioningExecutionReceipt public

berkeleyDiffuserCamRealConditioningExecutionReceipt :
  BerkeleyDiffuserCamRealConditioningExecutionReceipt
berkeleyDiffuserCamRealConditioningExecutionReceipt = record
  { calibrationArtifactPinned = Calibration.publicCalibrationArtifactPinned
  ; bytesVerified = realPSFArtifactBytesVerified
  ; identityVerified = realPSFArtifactIdentityVerified
  ; depthReceipt = depthOnlyNumericalReceiptCaptured
  ; translatedReceipt = translatedColumnNumericalReceiptCaptured
  ; finiteRestrictedKappa = finiteSelectedFamilyRestrictedKappaPaid
  ; plannerReceipt = realClaimScalePlannerReceiptCaptured
  ; allResolutionRIP = allResolutionCameraRIPPaid
  ; matchedPhoton = matchedPhotonComparisonPaid
  }
