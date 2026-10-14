module DASHI.Physics.Optics.Diffraction3DImagingAcquisitionMaxCutExact where

open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.Optics.Diffraction3DImagingPhysicalMaxCutExact as Physical
import DASHI.Physics.Optics.BerkeleyDiffuserCamPublicCalibrationExact as Calibration
import DASHI.Physics.Optics.BerkeleyDiffuserCamSourceOperatorExact as SourceOperator
import DASHI.Physics.Optics.BerkeleyDiffuserCamDepthConditioningExact as Conditioning
import DASHI.Physics.Optics.DiffuserCamLocalExecutionReceiptExact as LocalExecution
import DASHI.Physics.Optics.BerkeleyLenslessInformationDesignSourceExact as InfoSource
import DASHI.Physics.Optics.BerkeleyPhotonTransferCalibrationExact as PhotonTransfer
import DASHI.Physics.Optics.BerkeleyConvRMLParallelComparatorExact as ConvRML
import DASHI.Physics.Optics.BerkeleyPLDExposureProvenanceCoordinateExact as ExposureProvenance
import DASHI.Physics.Optics.BerkeleyPLD100kReleaseProvenanceExact as Release100k

------------------------------------------------------------------------
-- ACQUISITION MAX-CUT
--
-- Public-source acquisition has paid the literal Berkeley artifacts, source
-- operator semantics, an exact selected-grid compiler for columns of the pinned
-- discrete source H, executable depth / sparse conditioning diagnostics, the
-- 2026 information-design experiment, and the later 2026 ConvRML same-scene
-- parallel lens/diffuser/RML comparator geometry.
--
-- Local execution additionally pays three durable Git-blob-pinned receipts:
--   * a synthetic source-H implementation check covering odd/even shapes,
--     FFT-vs-kernel-shift agreement and every support of orders 1--3 on the
--     four declared fixtures (22,218 supports, zero violations);
--   * a synthetic claim-scale memory-plan execution over a declared geometry;
--   * a focused local pytest of the receipt wiring (2 passed, 0 failed).
-- The focused pytest is not promoted to full-repository pytest or Agda kernel
-- certification. None of these local receipts is promoted into the still-
-- unexecuted real Berkeley PSF receipt.
--
-- Photon transfer is now paid at a sharper level. The published executed
-- calibration notebook loads the simultaneous RML/Diffuser/lensed grayscale
-- sweep, fits variance against mean in a shot-noise regime, and applies
--   clip((image - intercept) / slope, 0, infinity)
-- to estimate detected photon counts. Recoverable displayed fits are
-- RML 0.02x+1.46, Diffuser 0.03x+0.36, Lens 0.05x+0.01. This pays a source-
-- executed detected-photon conversion surface, but not optical throughput,
-- incident-photon equality, or the hidden full-precision fit arrays.
--
-- The selected 100k PLD is also source-separated from the AWB 100k and AWB 25k
-- datasets in the public Drive. Its full-resolution RML branch is explicitly
-- partitioned 0--25k, 25--50k, 50--75k and 75--100k. Release-lineage capture
-- code from June through September pins RGB8, gain=0 and 25/80/18 ms in
-- diffuser/RML/ground-truth order. No per-archive run log was observed that
-- welds those code defaults to the exact archive bytes, so same-run exposure
-- identity remains fail-closed.
--
-- Remaining numerical/physical leaves are now:
--   A. execute/ingest the pinned binary PSF audit and retain its numerical
--      depth + selected-grid same-H sparse certificate receipt;
--   B. run the memory planner on the actual PSF dimensions, select the finite
--      lateral grid / sparsity class required by the intended 3-D claim, and
--      populate the same-H kappa producer from measured coherence/Gershgorin;
--   C. recover a per-run/per-archive acquisition log if exact same-run exposure
--      identity is required beyond the now-paid release lineage;
--   D. obtain optical-throughput / incident-photon calibration if the target is
--      a genuinely matched incident-photon acquisition-risk comparison;
--   E. add a Fresnel-zone-plate arm only if that optional stronger comparison
--      remains scientifically useful.
------------------------------------------------------------------------

record Diffraction3DImagingAcquisitionMaxCut : Set where
  field
    physicalInterfaceSpinePaid : Bool
    publicBerkeleyCalibrationArtifactPinned : Bool
    publicBerkeleySourceOperatorPinned : Bool
    offlineSyntheticOperatorSelfTestExecutable : Bool
    localSyntheticOperatorReceiptCaptured : Bool
    localExhaustiveFiniteSupportReceiptCaptured : Bool
    claimScaleMemoryPlannerExecutable : Bool
    localClaimScalePlannerReceiptCaptured : Bool
    localFocusedReceiptPytestCaptured : Bool
    fullRepositoryPytestCaptured : Bool
    agdaKernelReceiptCaptured : Bool
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
    sourceExecutedPhotonTransferCalibrationPinned : Bool
    detectedPhotonCountConversionPinned : Bool
    fullPrecisionPhotonTransferCoefficientsRecovered : Bool
    opticalThroughputCalibrationPinned : Bool
    physicalAcquisitionPhotonCalibrationPinned : Bool
    publishedRealRMLVsDiffuserCamComparisonPinned : Bool
    parallelLensDiffuserRMLAcquisitionPinned : Bool
    parallelSensorIlluminationGeometryPinned : Bool
    parallelExposureCalibrationPinned : Bool
    releasedCaptureGainAndFormatPinned : Bool
    exposureProvenanceCollisionFormalised : Bool
    main100kArchiveIdentityPinned : Bool
    releaseLineageCaptureParametersPinned : Bool
    exactArchiveExposureSameRunPaid : Bool
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
  ; localExhaustiveFiniteSupportReceiptCaptured = LocalExecution.exhaustiveFiniteSupportReceiptCaptured
  ; claimScaleMemoryPlannerExecutable = true
  ; localClaimScalePlannerReceiptCaptured = LocalExecution.claimScalePlannerReceiptCaptured
  ; localFocusedReceiptPytestCaptured = LocalExecution.focusedReceiptContractPytestCaptured
  ; fullRepositoryPytestCaptured = LocalExecution.fullRepositoryPytestCaptured
  ; agdaKernelReceiptCaptured = LocalExecution.agdaKernelReceiptCaptured
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
  ; sourceExecutedPhotonTransferCalibrationPinned = PhotonTransfer.sourceExecutedPhotonTransferCalibrationPaid
  ; detectedPhotonCountConversionPinned = PhotonTransfer.detectedPhotonCountConversionPinned
  ; fullPrecisionPhotonTransferCoefficientsRecovered = PhotonTransfer.fullPrecisionFitCoefficientsRecovered
  ; opticalThroughputCalibrationPinned = PhotonTransfer.opticalThroughputCalibrationPaid
  ; physicalAcquisitionPhotonCalibrationPinned = InfoSource.physicalAcquisitionPhotonCalibrationPaid
  ; publishedRealRMLVsDiffuserCamComparisonPinned = true
  ; parallelLensDiffuserRMLAcquisitionPinned = true
  ; parallelSensorIlluminationGeometryPinned = true
  ; parallelExposureCalibrationPinned = true
  ; releasedCaptureGainAndFormatPinned = true
  ; exposureProvenanceCollisionFormalised = true
  ; main100kArchiveIdentityPinned = Release100k.main100kArchiveIdentityPinned
  ; releaseLineageCaptureParametersPinned = Release100k.releaseLineageCaptureParametersPinned
  ; exactArchiveExposureSameRunPaid = Release100k.exactArchiveExposureSameRunPaid
  ; parallelExposureProvenanceReconciled = ExposureProvenance.exactDatasetExposureProvenancePaid
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

localExhaustiveSupportReceiptStatus : Bool
localExhaustiveSupportReceiptStatus = LocalExecution.exhaustiveFiniteSupportReceiptCaptured

claimScaleMemoryPlannerStatus : Bool
claimScaleMemoryPlannerStatus = Conditioning.claimScaleMemoryPlannerExecutable

localClaimScaleReceiptStatus : Bool
localClaimScaleReceiptStatus = LocalExecution.claimScalePlannerReceiptCaptured

localFocusedPytestReceiptStatus : Bool
localFocusedPytestReceiptStatus = LocalExecution.focusedReceiptContractPytestCaptured

fullRepositoryPytestReceiptStatus : Bool
fullRepositoryPytestReceiptStatus = LocalExecution.fullRepositoryPytestCaptured

agdaKernelReceiptStatus : Bool
agdaKernelReceiptStatus = LocalExecution.agdaKernelReceiptCaptured

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

sourceExecutedPhotonTransferStatus : Bool
sourceExecutedPhotonTransferStatus = PhotonTransfer.sourceExecutedPhotonTransferCalibrationPaid

detectedPhotonConversionStatus : Bool
detectedPhotonConversionStatus = PhotonTransfer.detectedPhotonCountConversionPinned

opticalThroughputCalibrationStatus : Bool
opticalThroughputCalibrationStatus = PhotonTransfer.opticalThroughputCalibrationPaid

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

main100kArchiveStatus : Bool
main100kArchiveStatus = Release100k.main100kArchiveIdentityPinned

releaseCaptureLineageStatus : Bool
releaseCaptureLineageStatus = Release100k.releaseLineageCaptureParametersPinned

archiveSameRunExposureStatus : Bool
archiveSameRunExposureStatus = Release100k.exactArchiveExposureSameRunPaid

exposureProvenanceStatus : Bool
exposureProvenanceStatus = ExposureProvenance.exactDatasetExposureProvenancePaid

matchedPhotonParallelStatus : Bool
matchedPhotonParallelStatus = ConvRML.matchedPhotonAcrossSystemsPaid

focusedThreeWaySourceStatus : Bool
focusedThreeWaySourceStatus = ConvRML.fresnelZonePlateArmPaid
