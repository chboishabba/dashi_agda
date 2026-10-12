module DASHI.Physics.Optics.BerkeleyDiffuserCamDepthConditioningExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Optics.BerkeleyDiffuserCamPublicCalibrationExact as Calibration
import DASHI.Physics.Optics.BerkeleyDiffuserCamSourceOperatorExact as SourceOperator
import DASHI.Physics.Optics.DiffuserRestrictedStabilityProducerExact as Stability

------------------------------------------------------------------------
-- EXECUTABLE NUMERICAL ACQUISITION BOUNDARY
--
-- scripts/check_waller_diffusercam_conditioning.py is pinned to the exact
-- public PSF artifact and exact source preprocessing (PSF bias = 102). It
-- computes a same-lateral depth-code matrix by vectorising each depth PSF,
-- then reports rank, Gram coherence and singular values.
--
-- This is deliberately weaker than the global restricted inverse obligation:
-- the full 3-D camera operator contains lateral translations of all depth
-- codewords, and a k-sparse/TV scene class requires support-uniform bounds on
-- those translated columns. A depth-only SVD cannot pay that theorem.
------------------------------------------------------------------------

conditioningAuditScript : String
conditioningAuditScript = "scripts/check_waller_diffusercam_conditioning.py"

publishedPSFArtifactUsed : Bool
publishedPSFArtifactUsed = true

depthOnlySameLateralAuditExecutable : Bool
depthOnlySameLateralAuditExecutable = true

-- The public binary is pinned, but no numerical run receipt was observed in
-- the current connector/runtime. Keep the result itself fail-closed.
depthOnlyNumericalReceiptCaptured : Bool
depthOnlyNumericalReceiptCaptured = false

translatedColumnRestrictedAuditPaid : Bool
translatedColumnRestrictedAuditPaid = false

globalSparseRestrictedKappaPaid : Bool
globalSparseRestrictedKappaPaid = false

record BerkeleyDiffuserCamDepthConditioningReceipt : Set where
  field
    psfArtifactPinned : Bool
    sourceOperatorPinned : Bool
    executableDepthAudit : Bool
    numericalDepthReceipt : Bool
    translatedColumnAudit : Bool
    globalRestrictedKappa : Bool

open BerkeleyDiffuserCamDepthConditioningReceipt public

currentBerkeleyDiffuserCamDepthConditioningReceipt :
  BerkeleyDiffuserCamDepthConditioningReceipt
currentBerkeleyDiffuserCamDepthConditioningReceipt = record
  { psfArtifactPinned = Calibration.publicCalibrationArtifactPinned
  ; sourceOperatorPinned = SourceOperator.sourceForwardUsesFFTConvolution
  ; executableDepthAudit = depthOnlySameLateralAuditExecutable
  ; numericalDepthReceipt = depthOnlyNumericalReceiptCaptured
  ; translatedColumnAudit = translatedColumnRestrictedAuditPaid
  ; globalRestrictedKappa = globalSparseRestrictedKappaPaid
  }

-- Importing Stability binds the numerical acquisition target to the existing
-- same-H restricted-stability producer. This module does not create a second
-- inverse theorem or substitute a depth-only condition number for kappa.
