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
-- Public-source acquisition pays the literal Berkeley artifacts/source operator,
-- the 2026 information-design experiment, the ConvRML parallel comparator, and
-- an executed photon-transfer notebook for RML/Diffuser/lensed detector counts.
-- Local execution separately pays synthetic source-H, finite-support, memory-
-- planner and focused receipt-wiring receipts. None is promoted into the still-
-- unavailable real `example_psfs.mat` execution receipt.
--
-- Photon transfer is now deliberately split into distinct claims:
--   * source-executed DN -> estimated detected-photon calibration: PAID;
--   * local re-execution of the multi-GB raw grayscale sweep: UNPAID;
--   * incident-photon optical throughput / matched input flux: UNPAID.
--
-- The selected 100k PLD is source-separated from the AWB datasets. Release-
-- lineage capture code from June through September pins RGB8, gain=0 and
-- 25/80/18 ms in diffuser/RML/ground-truth order. A per-archive same-run log
-- has not been recovered, so exact archive exposure identity stays fail-closed.
--
-- Remaining physical/execution leaves:
--   A. execute the pinned 10.8 MB PSF binary and retain real same-H diagnostics;
--   B. run the memory planner on the actual PSF shape and selected scene class;
--   C. recover same-run archive/capture provenance if stronger than release
--      lineage is required;
--   D. obtain optical-throughput / incident-photon calibration for a genuinely
--      matched physical input-photon comparison;
--   E. optional FZP arm only if the stronger three-way comparison is retained.
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
    sourceDigitalToEstimatedPhotonConversionPinned : Bool
    detectedPhotonCountConversionPinned : Bool
    localRawPhotonCalibrationReexecuted : Bool
    fullPrecisionPhotonTransferCoefficientsRecovered : Bool
    incidentPhotonThroughputCalibrationPinned : Bool
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
  ; sourceExecutedPhotonTransferCalibrationPinned = true
  ; sourceDigitalToEstimatedPhotonConversionPinned = true
  ; detectedPhotonCountConversionPinned = PhotonTransfer.detectedPhotonCountConversionPinned
  ; localRawPhotonCalibrationReexecuted = false
  ; fullPrecisionPhotonTransferCoefficientsRecovered = PhotonTransfer.fullPrecisionFitCoefficientsRecovered
  ; incidentPhotonThroughputCalibrationPinned = false
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
sourceDigitalPhotonConversionStatus : Bool
sourceDigitalPhotonConversionStatus = PhotonTransfer.sourceDigitalToEstimatedPhotonConversionPaid
localRawPhotonCalibrationStatus : Bool
localRawPhotonCalibrationStatus = PhotonTransfer.localRawCalibrationSweepReexecuted
incidentPhotonThroughputStatus : Bool
incidentPhotonThroughputStatus = PhotonTransfer.incidentPhotonThroughputCalibrationPaid
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
