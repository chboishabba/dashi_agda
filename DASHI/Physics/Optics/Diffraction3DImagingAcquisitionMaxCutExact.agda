module DASHI.Physics.Optics.Diffraction3DImagingAcquisitionMaxCutExact where

open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.Optics.Diffraction3DImagingPhysicalMaxCutExact as Physical
import DASHI.Physics.Optics.BerkeleyDiffuserCamPublicCalibrationExact as Calibration
import DASHI.Physics.Optics.BerkeleyDiffuserCamSourceOperatorExact as SourceOperator
import DASHI.Physics.Optics.BerkeleyDiffuserCamDepthConditioningExact as Conditioning
import DASHI.Physics.Optics.DiffuserCamLocalExecutionReceiptExact as LocalExecution
import DASHI.Physics.Optics.BerkeleyLenslessInformationDesignSourceExact as InfoSource
import DASHI.Physics.Optics.BerkeleyConvRMLParallelComparatorExact as ConvRML
import DASHI.Physics.Optics.BerkeleyPLDExposureProvenanceCoordinateExact as ExposureProvenance

------------------------------------------------------------------------
-- ACQUISITION MAX-CUT
--
-- Public-source acquisition has paid the literal Berkeley artifacts, source
-- operator semantics, an exact selected-grid compiler for columns of the pinned
-- discrete source H, executable depth / sparse conditioning diagnostics, the
-- 2026 information-design experiment, and the later 2026 ConvRML same-scene
-- parallel lens/diffuser/RML comparator geometry.
--
-- Local execution now additionally pays two durable, SHA-pinned receipts:
--   * a synthetic source-H implementation check covering odd/even shapes,
--     FFT-vs-kernel-shift agreement and 500 randomized Gershgorin support tests;
--   * a synthetic claim-scale memory-plan execution over a declared geometry.
-- These are captured execution receipts, not merely executable code. They remain
-- deliberately separate from the still-unexecuted real Berkeley PSF receipt.
--
-- The information-design code additionally pays a common *analysis* photon
-- normalization: each real dataset is divided by its own mean, rescaled to a
-- synthetic mean count of 500, biased by 10 and evaluated with a Poisson noise
-- model. This is not physical acquisition-photon calibration.
--
-- ConvRML further pays identical sensor model, common illumination / approximate
-- magnification matching, publication exposure calibration, and released-code
-- RGB8 + zero-gain controls. The publication and released capture script expose
-- different exposure triples. ExperimentalCoordinateDesign is reused to prove
-- that dataset-tranche provenance separates worlds collapsed by the generic
-- PLD label, while the paper and older AWB worlds can share one exposure profile.
-- Thus exposure equality alone cannot identify the selected dataset.
--
-- Remaining numerical/physical leaves are now:
--   A. execute/ingest the pinned binary PSF audit and retain its numerical
--      depth + selected-grid same-H sparse certificate receipt;
--   B. run the memory planner on the actual PSF dimensions, select the finite
--      lateral grid / sparsity class required by the intended 3-D claim, and
--      populate the same-H kappa producer from measured coherence/Gershgorin;
--   C. recover the same-object capture/run provenance for the selected 100k PLD
--      tranche, then obtain physical throughput / incident-or-detected-photon
--      calibration for a genuinely matched-photon acquisition-risk comparison;
--   D. add a Fresnel-zone-plate arm only if that optional stronger comparison
--      remains scientifically useful.
------------------------------------------------------------------------

record Diffraction3DImagingAcquisitionMaxCut : Set where
  field
    physicalInterfaceSpinePaid : Bool
    publicBerkeleyCalibrationArtifactPinned : Bool
    publicBerkeleySourceOperatorPinned : Bool
    offlineSyntheticOperatorSelfTestExecutable : Bool
    localSyntheticOperatorReceiptCaptured : Bool
    claimScaleMemoryPlannerExecutable : Bool
    localClaimScalePlannerReceiptCaptured : Bool
    sourceOperatorSelectedGridColumnCompilerPaid : Bool
    depthConditioningAuditExecutable : Bool
    translatedColumnRestrictedAuditExecutable : Bool
    coherenceSparseLowerBoundCompilerPaid : Bool
    berkeleyNumericPSFArrayIngested : Bool
    depthOnlyNumericalReceiptCaptured : Bool
    translatedColumnNumericalReceiptCaptured : Bool
    sameHRestrictedConditionNumberMeasured : Bool
    publishedInformationDesignExperimentPinned : Bool
    matchedAnalysisPhotonNormalizationPinned : Bool
    physicalAcquisitionPhotonCalibrationPinned : Bool
    publishedRealRMLVsDiffuserCamComparisonPinned : Bool
    parallelLensDiffuserRMLAcquisitionPinned : Bool
    parallelSensorIlluminationGeometryPinned : Bool
    parallelExposureCalibrationPinned : Bool
    releasedCaptureGainAndFormatPinned : Bool
    exposureProvenanceCollisionFormalised : Bool
    parallelExposureProvenanceReconciled : Bool
    matchedPhotonAcrossParallelSystems : Bool
    focusedLensDiffuserFZPMatchedPhotonReceipt : Bool

open Diffraction3DImagingAcquisitionMaxCut public

currentDiffraction3DImagingAcquisitionMaxCut : Diffraction3DImagingAcquisitionMaxCut
currentDiffraction3DImagingAcquisitionMaxCut = record
  { physicalInterfaceSpinePaid = true
  ; publicBerkeleyCalibrationArtifactPinned = true
  ; publicBerkeleySourceOperatorPinned = true
  ; offlineSyntheticOperatorSelfTestExecutable = true
  ; localSyntheticOperatorReceiptCaptured = LocalExecution.syntheticOperatorReceiptCaptured
  ; claimScaleMemoryPlannerExecutable = true
  ; localClaimScalePlannerReceiptCaptured = LocalExecution.claimScalePlannerReceiptCaptured
  ; sourceOperatorSelectedGridColumnCompilerPaid = true
  ; depthConditioningAuditExecutable = true
  ; translatedColumnRestrictedAuditExecutable = true
  ; coherenceSparseLowerBoundCompilerPaid = true
  ; berkeleyNumericPSFArrayIngested = false
  ; depthOnlyNumericalReceiptCaptured = false
  ; translatedColumnNumericalReceiptCaptured = false
  ; sameHRestrictedConditionNumberMeasured = false
  ; publishedInformationDesignExperimentPinned = true
  ; matchedAnalysisPhotonNormalizationPinned = true
  ; physicalAcquisitionPhotonCalibrationPinned = false
  ; publishedRealRMLVsDiffuserCamComparisonPinned = true
  ; parallelLensDiffuserRMLAcquisitionPinned = true
  ; parallelSensorIlluminationGeometryPinned = true
  ; parallelExposureCalibrationPinned = true
  ; releasedCaptureGainAndFormatPinned = true
  ; exposureProvenanceCollisionFormalised = true
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

offlineSyntheticSelfTestStatus : Bool
offlineSyntheticSelfTestStatus = Conditioning.offlineSyntheticOperatorSelfTestExecutable

localSyntheticReceiptStatus : Bool
localSyntheticReceiptStatus = LocalExecution.syntheticOperatorReceiptCaptured

claimScaleMemoryPlannerStatus : Bool
claimScaleMemoryPlannerStatus = Conditioning.claimScaleMemoryPlannerExecutable

localClaimScaleReceiptStatus : Bool
localClaimScaleReceiptStatus = LocalExecution.claimScalePlannerReceiptCaptured

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

analysisPhotonNormalizationStatus : Bool
analysisPhotonNormalizationStatus = InfoSource.analysisPhotonNormalizationPaid

physicalPhotonCalibrationStatus : Bool
physicalPhotonCalibrationStatus = InfoSource.physicalAcquisitionPhotonCalibrationPaid

parallelComparatorSourceStatus : Bool
parallelComparatorSourceStatus = ConvRML.parallelLensDiffuserRMLAcquisitionPaid

parallelSensorStatus : Bool
parallelSensorStatus = ConvRML.identicalSensorModelPaid

parallelExposureStatus : Bool
parallelExposureStatus = ConvRML.exposureCalibrationPaid

releasedCaptureControlStatus : Bool
releasedCaptureControlStatus = ConvRML.releasedCaptureGainZeroPaid

exposureProvenanceCollisionStatus : Bool
exposureProvenanceCollisionStatus = ExposureProvenance.exposureProvenanceCollisionFormalised

exposureProvenanceStatus : Bool
exposureProvenanceStatus = ExposureProvenance.exactDatasetExposureProvenancePaid

matchedPhotonParallelStatus : Bool
matchedPhotonParallelStatus = ConvRML.matchedPhotonAcrossSystemsPaid

focusedThreeWaySourceStatus : Bool
focusedThreeWaySourceStatus = ConvRML.fresnelZonePlateArmPaid
