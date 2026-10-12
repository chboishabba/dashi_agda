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
-- operator semantics, an exact selected-grid compiler for columns of the pinned
-- discrete source H, executable depth / sparse conditioning diagnostics, the
-- 2026 information-design experiment, and the later 2026 ConvRML same-scene
-- parallel lens/diffuser/RML comparator geometry.
--
-- ConvRML further pays identical sensor model, common illumination / approximate
-- magnification matching, publication exposure calibration, and released-code
-- RGB8 + zero-gain controls. The publication and released capture script expose
-- different exposure triples; that same-dataset provenance seam stays explicit.
--
-- Remaining numerical/physical leaves are now:
--   A. execute/ingest the pinned binary PSF audit and retain its numerical
--      depth + selected-grid same-H sparse certificate receipt;
--   B. select the lateral grid / sparsity class at the scale required by the
--      intended 3-D claim and populate the existing same-H kappa producer from
--      the measured coherence/Gershgorin lower bound;
--   C. reconcile exact-dataset exposure provenance, then obtain throughput /
--      incident-or-detected-photon calibration sufficient for a genuinely
--      matched-photon cross-system risk comparison;
--   D. add a Fresnel-zone-plate arm only if that optional stronger comparison
--      remains scientifically useful.
------------------------------------------------------------------------

record Diffraction3DImagingAcquisitionMaxCut : Set where
  field
    physicalInterfaceSpinePaid : Bool
    publicBerkeleyCalibrationArtifactPinned : Bool
    publicBerkeleySourceOperatorPinned : Bool
    sourceOperatorSelectedGridColumnCompilerPaid : Bool
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
    releasedCaptureGainAndFormatPinned : Bool
    parallelExposureProvenanceReconciled : Bool
    matchedPhotonAcrossParallelSystems : Bool
    focusedLensDiffuserFZPMatchedPhotonReceipt : Bool

open Diffraction3DImagingAcquisitionMaxCut public

currentDiffraction3DImagingAcquisitionMaxCut : Diffraction3DImagingAcquisitionMaxCut
currentDiffraction3DImagingAcquisitionMaxCut = record
  { physicalInterfaceSpinePaid = true
  ; publicBerkeleyCalibrationArtifactPinned = true
  ; publicBerkeleySourceOperatorPinned = true
  ; sourceOperatorSelectedGridColumnCompilerPaid = true
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
  ; releasedCaptureGainAndFormatPinned = true
  ; parallelExposureProvenanceReconciled = false
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

sourceSelectedGridCompilerStatus : Bool
sourceSelectedGridCompilerStatus = Conditioning.sourceOperatorSelectedGridColumnCompilerPaid

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

releasedCaptureControlStatus : Bool
releasedCaptureControlStatus = ConvRML.releasedCaptureGainZeroPaid

exposureProvenanceStatus : Bool
exposureProvenanceStatus = ConvRML.exactDatasetExposureIdentityReconciled

matchedPhotonParallelStatus : Bool
matchedPhotonParallelStatus = ConvRML.matchedPhotonAcrossSystemsPaid

focusedThreeWaySourceStatus : Bool
focusedThreeWaySourceStatus = ConvRML.fresnelZonePlateArmPaid
