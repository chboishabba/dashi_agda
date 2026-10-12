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
-- public PSF artifact and source preprocessing. It now has two scopes:
--
-- 1. same-lateral depth-code SVD / Gram diagnostics;
-- 2. a declared finite lateral translation grid, using zero-fill shifted PSFs
--    cropped back to the sensor rectangle, followed by normalized mutual
--    coherence and a Gershgorin sparse lower-bound compiler.
--
-- The second route can produce a genuine restricted inverse certificate for
-- exactly the finite translated-column scene family executed by the script.
-- It is not promoted to an all-resolution camera RIP theorem, and no numeric
-- certificate is claimed until the pinned binary artifact is actually run.
------------------------------------------------------------------------

conditioningAuditScript : String
conditioningAuditScript = "scripts/check_waller_diffusercam_conditioning.py"

publishedPSFArtifactUsed : Bool
publishedPSFArtifactUsed = true

depthOnlySameLateralAuditExecutable : Bool
depthOnlySameLateralAuditExecutable = true

translatedColumnRestrictedAuditExecutable : Bool
translatedColumnRestrictedAuditExecutable = true

coherenceToSparseLowerBoundCompilerPaid : Bool
coherenceToSparseLowerBoundCompilerPaid = true

-- The public binary is pinned, but no numerical run receipt was observed in
-- the current connector/runtime. Keep numerical promotions fail-closed.
depthOnlyNumericalReceiptCaptured : Bool
depthOnlyNumericalReceiptCaptured = false

translatedColumnNumericalReceiptCaptured : Bool
translatedColumnNumericalReceiptCaptured = false

globalSparseRestrictedKappaPaid : Bool
globalSparseRestrictedKappaPaid = false

record BerkeleyDiffuserCamDepthConditioningReceipt : Set where
  field
    psfArtifactPinned : Bool
    sourceOperatorPinned : Bool
    executableDepthAudit : Bool
    executableTranslatedColumnAudit : Bool
    sparseLowerBoundCompiler : Bool
    numericalDepthReceipt : Bool
    numericalTranslatedColumnReceipt : Bool
    globalRestrictedKappa : Bool

open BerkeleyDiffuserCamDepthConditioningReceipt public

currentBerkeleyDiffuserCamDepthConditioningReceipt :
  BerkeleyDiffuserCamDepthConditioningReceipt
currentBerkeleyDiffuserCamDepthConditioningReceipt = record
  { psfArtifactPinned = Calibration.publicCalibrationArtifactPinned
  ; sourceOperatorPinned = SourceOperator.sourceForwardUsesFFTConvolution
  ; executableDepthAudit = depthOnlySameLateralAuditExecutable
  ; executableTranslatedColumnAudit = translatedColumnRestrictedAuditExecutable
  ; sparseLowerBoundCompiler = coherenceToSparseLowerBoundCompilerPaid
  ; numericalDepthReceipt = depthOnlyNumericalReceiptCaptured
  ; numericalTranslatedColumnReceipt = translatedColumnNumericalReceiptCaptured
  ; globalRestrictedKappa = globalSparseRestrictedKappaPaid
  }

-- Importing Stability binds a successful finite numerical certificate to the
-- existing same-H restricted-stability producer. This module does not create a
-- second inverse theorem or extrapolate a finite grid certificate beyond its
-- declared admissible scene family.
