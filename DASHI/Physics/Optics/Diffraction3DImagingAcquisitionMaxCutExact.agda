module DASHI.Physics.Optics.Diffraction3DImagingAcquisitionMaxCutExact where

open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.Optics.Diffraction3DImagingPhysicalMaxCutExact as Physical
import DASHI.Physics.Optics.BerkeleyDiffuserCamPublicCalibrationExact as Calibration
import DASHI.Physics.Optics.BerkeleyDiffuserCamSourceOperatorExact as SourceOperator
import DASHI.Physics.Optics.BerkeleyDiffuserCamDepthConditioningExact as Conditioning
import DASHI.Physics.Optics.BerkeleyLenslessInformationDesignSourceExact as InfoSource

------------------------------------------------------------------------
-- ACQUISITION MAX-CUT
--
-- Public-source acquisition has paid the literal Berkeley artifacts, source
-- operator semantics, an executable same-artifact depth-conditioning audit,
-- and the published 2026 information-design / real parallel-lensless surface.
--
-- Remaining numerical/physical leaves are now sharply separated:
--   A. execute/ingest the pinned binary PSF audit and retain its numeric receipt;
--   B. extend from same-lateral depth columns to translated 3-D columns and
--      prove/measure a support-uniform restricted bound for the declared scene
--      class, thereby populating the existing same-H kappa producer;
--   C. obtain a genuine focused-lens / diffuser / FZP matched-photon receipt
--      only if that stronger three-way comparison remains a target.
------------------------------------------------------------------------

record Diffraction3DImagingAcquisitionMaxCut : Set where
  field
    physicalInterfaceSpinePaid : Bool
    publicBerkeleyCalibrationArtifactPinned : Bool
    publicBerkeleySourceOperatorPinned : Bool
    depthConditioningAuditExecutable : Bool
    berkeleyNumericPSFArrayIngested : Bool
    depthOnlyNumericalReceiptCaptured : Bool
    translatedColumnRestrictedAuditPaid : Bool
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
  ; depthConditioningAuditExecutable = true
  ; berkeleyNumericPSFArrayIngested = false
  ; depthOnlyNumericalReceiptCaptured = false
  ; translatedColumnRestrictedAuditPaid = false
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

depthAuditExecutableStatus : Bool
depthAuditExecutableStatus = Conditioning.depthOnlySameLateralAuditExecutable

depthNumericReceiptStatus : Bool
depthNumericReceiptStatus = Conditioning.depthOnlyNumericalReceiptCaptured

translatedAuditStatus : Bool
translatedAuditStatus = Conditioning.translatedColumnRestrictedAuditPaid

restrictedKappaStatus : Bool
restrictedKappaStatus = Conditioning.globalSparseRestrictedKappaPaid

informationExperimentSourceStatus : Bool
informationExperimentSourceStatus = InfoSource.informationOptimalEncoderExperimentPinned

focusedThreeWaySourceStatus : Bool
focusedThreeWaySourceStatus = InfoSource.focusedLensFZPComparisonPaid
