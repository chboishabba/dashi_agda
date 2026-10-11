module DASHI.Physics.Optics.Diffraction3DImagingAcquisitionMaxCutExact where

open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.Optics.Diffraction3DImagingPhysicalMaxCutExact as Physical
import DASHI.Physics.Optics.BerkeleyDiffuserCamPublicCalibrationExact as Calibration
import DASHI.Physics.Optics.BerkeleyDiffuserCamSourceOperatorExact as SourceOperator
import DASHI.Physics.Optics.BerkeleyLenslessInformationDesignSourceExact as InfoSource

------------------------------------------------------------------------
-- ACQUISITION MAX-CUT
--
-- Public-source acquisition has now paid the literal Berkeley artifact and
-- source-code identities plus the published 2026 information-design / real
-- parallel-lensless experiment surface.  The remaining leaves are narrower:
-- decode/materialise the numeric PSF stack, derive a restricted stability
-- constant for exactly that H and admitted scene family, and obtain a genuine
-- focused-lens / diffuser / FZP matched-photon comparator if that three-way
-- claim is desired.
------------------------------------------------------------------------

record Diffraction3DImagingAcquisitionMaxCut : Set where
  field
    physicalInterfaceSpinePaid : Bool
    publicBerkeleyCalibrationArtifactPinned : Bool
    publicBerkeleySourceOperatorPinned : Bool
    berkeleyNumericPSFArrayIngested : Bool
    sameHRestrictedConditionNumberMeasured : Bool
    publishedInformationDesignExperimentPinned : Bool
    publishedRealRMLVsDiffuserCamComparisonPinned : Bool
    focusedLensDiffuserFZPMatchedPhotonReceipt : Bool

open Diffraction3DImagingAcquisitionMaxCut public

currentDiffraction3DImagingAcquisitionMaxCut : Diffraction3DImagingAcquisitionMaxCut
currentDiffraction3DImagingAcquisitionMaxCut = record
  { physicalInterfaceSpinePaid = true
  ; publicBerkeleyCalibrationArtifactPinned = true
  ; publicBerkeleySourceOperatorPinned = true
  ; berkeleyNumericPSFArrayIngested = false
  ; sameHRestrictedConditionNumberMeasured = false
  ; publishedInformationDesignExperimentPinned = true
  ; publishedRealRMLVsDiffuserCamComparisonPinned = true
  ; focusedLensDiffuserFZPMatchedPhotonReceipt = false
  }

-- Non-collapse sanity aliases bind the ledger to source owners rather than
-- free-floating booleans.
calibrationArtifactSourceStatus : Bool
calibrationArtifactSourceStatus = Calibration.publicCalibrationArtifactPinned

numericPSFSourceStatus : Bool
numericPSFSourceStatus = Calibration.numericPSFArrayIngested

sourceOperatorMaterialisationStatus : Bool
sourceOperatorMaterialisationStatus = SourceOperator.numericOperatorMatrixMaterialised

informationExperimentSourceStatus : Bool
informationExperimentSourceStatus = InfoSource.informationOptimalEncoderExperimentPinned

focusedThreeWaySourceStatus : Bool
focusedThreeWaySourceStatus = InfoSource.focusedLensFZPComparisonPaid
