module DASHI.Physics.Optics.Diffraction3DImagingAcquisitionMaxCutExact where

open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.Optics.Diffraction3DImagingPhysicalMaxCutExact as Physical
import DASHI.Physics.Optics.BerkeleyDiffuserCamPublicCalibrationExact as Calibration
import DASHI.Physics.Optics.BerkeleyDiffuserCamSourceOperatorExact as SourceOperator
import DASHI.Physics.Optics.BerkeleyDiffuserCamDepthConditioningExact as Conditioning
import DASHI.Physics.Optics.BerkeleyLenslessInformationDesignSourceExact as InfoSource
import DASHI.Physics.Optics.BerkeleyConvRMLParallelComparatorExact as ConvRML

------------------------------------------------------------------------
-- ACQUISITION MAX-CUT
--
-- Public-source acquisition has paid the literal Berkeley artifacts, source
-- operator semantics, executable depth and finite translated-column sparse
-- certificate producers, the 2026 information-design experiment, and the later
-- 2026 ConvRML same-scene parallel lens/diffuser/RML comparator geometry.
-- ConvRML further pays identical sensor model, same illumination / approximate
-- magnification matching, and explicit exposure calibration; its unequal
-- 80/50/4 ms exposures prevent any silent equal-exposure/photon promotion.
--
-- Remaining numerical/physical leaves are now:
--   A. execute/ingest the pinned binary PSF audit and retain its numerical
--      depth + finite translated-column certificate receipt;
--   B. choose/execute the declared lateral grid / sparsity class at the scale
--      needed for the intended 3-D claim and populate the existing same-H kappa
--      producer from the measured coherence/Gershgorin lower bound;
--   C. obtain throughput / incident-or-detected-photon calibration sufficient
--      for a genuinely matched-photon cross-system risk comparison;
--   D. add a Fresnel-zone-plate arm only if that optional stronger comparison
--      remains scientifically useful.
------------------------------------------------------------------------

record Diffraction3DImagingAcquisitionMaxCut : Set where
  field
    physicalInterfaceSpinePaid : Bool
    publicBerkeleyCalibrationArtifactPinned : Bool
    publicBerkeleySourceOperatorPinned : Bool
    depthConditioningAuditExecutable : Bool
    translatedColumnRestrictedAuditExecutable : Bool
    coherenceSparseLowerBoundCompilerPaid : Bool
    berkeleyNumericPSFArrayIngested : Bool
    depthOnlyNumericalReceiptCaptured : Bool
    translatedColumnNumericalReceiptCaptured : Bool
    sameHRestrictedConditionNumberMeasured : Bool
    publishedInformationDesignExperimentPinned : Bool
    publishedRealRMLVsDiffuserCamComparisonPinned : Bool
    parallelLensDiffuserRMLAcquisitionPinned : Bool
    parallelSensorIlluminationGeometryPinned : Bool
    parallelExposureCalibrationPinned : Bool
    matchedPhotonAcrossParallelSystems : Bool
    focusedLensDiffuserFZPMatchedPhotonReceipt : Bool

open Diffraction3DImagingAcquisitionMaxCut public

currentDiffraction3DImagingAcquisitionMaxCut : Diffraction3DImagingAcquisitionMaxCut
currentDiffraction3DImagingAcquisitionMaxCut = record
  { physicalInterfaceSpinePaid = true
  ; publicBerkeleyCalibrationArtifactPinned = true
  ; publicBerkeleySourceOperatorPinned = true
  ; depthConditioningAuditExecutable = true
  ; translatedColumnRestrictedAuditExecutable = true
  ; coherenceSparseLowerBoundCompilerPaid = true
  ; berkeleyNumericPSFArrayIngested = false
  ; depthOnlyNumericalReceiptCaptured = false
  ; translatedColumnNumericalReceiptCaptured = false
  ; sameHRestrictedConditionNumberMeasured = false
  ; publishedInformationDesignExperimentPinned = true
  ; publishedRealRMLVsDiffuserCamComparisonPinned = true
  ; parallelLensDiffuserRMLAcquisitionPinned = true
  ; parallelSensorIlluminationGeometryPinned = true
  ; parallelExposureCalibrationPinned = true
  ; matchedPhotonAcrossParallelSystems = false
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

translatedAuditExecutableStatus : Bool
translatedAuditExecutableStatus = Conditioning.translatedColumnRestrictedAuditExecutable

sparseLowerBoundCompilerStatus : Bool
sparseLowerBoundCompilerStatus = Conditioning.coherenceToSparseLowerBoundCompilerPaid

depthNumericReceiptStatus : Bool
depthNumericReceiptStatus = Conditioning.depthOnlyNumericalReceiptCaptured

translatedNumericReceiptStatus : Bool
translatedNumericReceiptStatus = Conditioning.translatedColumnNumericalReceiptCaptured

restrictedKappaStatus : Bool
restrictedKappaStatus = Conditioning.globalSparseRestrictedKappaPaid

informationExperimentSourceStatus : Bool
informationExperimentSourceStatus = InfoSource.informationOptimalEncoderExperimentPinned

parallelComparatorSourceStatus : Bool
parallelComparatorSourceStatus = ConvRML.parallelLensDiffuserRMLAcquisitionPaid

parallelSensorStatus : Bool
parallelSensorStatus = ConvRML.identicalSensorModelPaid

parallelExposureStatus : Bool
parallelExposureStatus = ConvRML.exposureCalibrationPaid

matchedPhotonParallelStatus : Bool
matchedPhotonParallelStatus = ConvRML.matchedPhotonAcrossSystemsPaid

focusedThreeWaySourceStatus : Bool
focusedThreeWaySourceStatus = ConvRML.fresnelZonePlateArmPaid
