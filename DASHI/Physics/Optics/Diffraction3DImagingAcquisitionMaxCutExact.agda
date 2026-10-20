module DASHI.Physics.Optics.Diffraction3DImagingAcquisitionMaxCutExact where

open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.Optics.Diffraction3DImagingPhysicalMaxCutExact as Physical
import DASHI.Physics.Optics.BerkeleyDiffuserCamPublicCalibrationExact as Calibration
import DASHI.Physics.Optics.BerkeleyDiffuserCamSourceOperatorExact as SourceOperator
import DASHI.Physics.Optics.BerkeleyDiffuserCamDepthConditioningExact as Conditioning
import DASHI.Physics.Optics.BerkeleyDiffuserCamRealConditioningExecutionExact as RealConditioning
import DASHI.Physics.Optics.DiffuserCamLocalExecutionReceiptExact as LocalExecution
import DASHI.Physics.Optics.BerkeleyLenslessInformationDesignSourceExact as InfoSource
import DASHI.Physics.Optics.BerkeleyPhotonTransferCalibrationExact as PhotonTransfer
import DASHI.Physics.Optics.BerkeleyPhotonTransferLocalExecutionReceiptExact as PhotonTransferLocal
import DASHI.Physics.Optics.BerkeleySystemCharacterizationDetectedPhotonExact as SystemCharacterization
import DASHI.Physics.Optics.BerkeleyConvRMLParallelComparatorExact as ConvRML
import DASHI.Physics.Optics.BerkeleyPLDExposureProvenanceCoordinateExact as ExposureProvenance
import DASHI.Physics.Optics.BerkeleyPLD100kReleaseProvenanceExact as Release100k

------------------------------------------------------------------------
-- ACQUISITION MAX-CUT
--
-- Public-source acquisition pays the Berkeley artifacts/source operator, the
-- information-design experiment, the ConvRML comparator, source-executed
-- detector photon-transfer calibration, and publication-level provenance for
-- the synchronized 100k PLD. Local execution pays synthetic source-H / finite-
-- support / memory-planner / photon-transfer compiler receipts, real measured
-- characterization, and now the exact pinned Waller example_psfs.mat same-H
-- conditioning execution.
--
-- Important non-collapse boundaries:
--   * real Waller PSF bytes + finite same-H radius-1 receipt: PAID;
--   * all-resolution camera RIP or k>=2 coherence guarantee: UNPAID;
--   * published 100k acquisition exposure identity: PAID (80/50/4 ms);
--   * exact released-archive run-log identity: UNPAID;
--   * detected DN -> photon-count calibration: PAID;
--   * real measured characterization in detected-photon units: PAID;
--   * characterization exposure-normalized response: UNPAID;
--   * incident-photon optical throughput / matched input flux: UNPAID.
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
    localSyntheticPhotonTransferReceiptCaptured : Bool
    realSystemCharacterizationDetectedPhotonReceiptCaptured : Bool
    detectedPhotonCountConversionPinned : Bool
    localRawPhotonCalibrationReexecuted : Bool
    fullPrecisionPhotonTransferCoefficientsRecovered : Bool
    characterizationExposureNormalizedResponsePaid : Bool
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
    published100kAcquisitionProvenancePinned : Bool
    published100kExposureIdentityPinned : Bool
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
  ; localClaimScalePlannerReceiptCaptured = RealConditioning.realClaimScalePlannerReceiptCaptured
  ; localFocusedReceiptPytestCaptured = LocalExecution.focusedReceiptContractPytestCaptured
  ; fullRepositoryPytestCaptured = LocalExecution.fullRepositoryPytestCaptured
  ; agdaKernelReceiptCaptured = LocalExecution.agdaKernelReceiptCaptured
  ; sourceOperatorSelectedGridColumnCompilerPaid = true
  ; depthConditioningAuditExecutable = true
  ; translatedColumnRestrictedAuditExecutable = true
  ; coherenceSparseLowerBoundCompilerPaid = true
  ; berkeleyNumericPSFArrayIngested = RealConditioning.realPSFArtifactIdentityVerified
  ; depthOnlyNumericalReceiptCaptured = Conditioning.depthOnlyNumericalReceiptCaptured
  ; translatedColumnNumericalReceiptCaptured = Conditioning.translatedColumnNumericalReceiptCaptured
  ; sameHRestrictedConditionNumberMeasured = Conditioning.globalSparseRestrictedKappaPaid
  ; publishedInformationDesignExperimentPinned = true
  ; matchedAnalysisPhotonNormalizationPinned = true
  ; sourceExecutedPhotonTransferCalibrationPinned = true
  ; sourceDigitalToEstimatedPhotonConversionPinned = true
  ; localSyntheticPhotonTransferReceiptCaptured = PhotonTransferLocal.localSyntheticPhotonTransferReceiptCaptured
  ; realSystemCharacterizationDetectedPhotonReceiptCaptured = SystemCharacterization.detectedPhotonCharacterizationPaid
  ; detectedPhotonCountConversionPinned = PhotonTransfer.detectedPhotonCountConversionPinned
  ; localRawPhotonCalibrationReexecuted = PhotonTransfer.localRawCalibrationSweepReexecuted
  ; fullPrecisionPhotonTransferCoefficientsRecovered = PhotonTransfer.fullPrecisionFitCoefficientsRecovered
  ; characterizationExposureNormalizedResponsePaid = SystemCharacterization.exposureNormalizedResponsePaid
  ; incidentPhotonThroughputCalibrationPinned = PhotonTransfer.incidentPhotonThroughputCalibrationPaid
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
  ; published100kAcquisitionProvenancePinned = true
  ; published100kExposureIdentityPinned = true
  ; exactArchiveExposureSameRunPaid = Release100k.exactArchiveExposureSameRunPaid
  ; parallelExposureProvenanceReconciled = ExposureProvenance.exactDatasetExposureProvenancePaid
  ; matchedPhotonAcrossParallelSystems = false
  ; focusedLensDiffuserFZPMatchedPhotonReceipt = false
  }

calibrationArtifactSourceStatus : Bool
calibrationArtifactSourceStatus = Calibration.publicCalibrationArtifactPinned
numericPSFSourceStatus : Bool
numericPSFSourceStatus = RealConditioning.realPSFArtifactIdentityVerified
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
localClaimScaleReceiptStatus = RealConditioning.realClaimScalePlannerReceiptCaptured
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
localSyntheticPhotonTransferStatus : Bool
localSyntheticPhotonTransferStatus = PhotonTransferLocal.localSyntheticPhotonTransferReceiptCaptured
realCharacterizationDetectedPhotonStatus : Bool
realCharacterizationDetectedPhotonStatus = SystemCharacterization.detectedPhotonCharacterizationPaid
characterizationExposureNormalizedStatus : Bool
characterizationExposureNormalizedStatus = SystemCharacterization.exposureNormalizedResponsePaid
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
published100kAcquisitionStatus : Bool
published100kAcquisitionStatus = Release100k.published100kAcquisitionProvenancePaid
published100kExposureStatus : Bool
published100kExposureStatus = Release100k.published100kExposureIdentityPaid
archiveSameRunExposureStatus : Bool
archiveSameRunExposureStatus = Release100k.exactArchiveExposureSameRunPaid
exposureProvenanceStatus : Bool
exposureProvenanceStatus = ExposureProvenance.exactDatasetExposureProvenancePaid
matchedPhotonParallelStatus : Bool
matchedPhotonParallelStatus = ConvRML.matchedPhotonAcrossSystemsPaid
focusedThreeWaySourceStatus : Bool
focusedThreeWaySourceStatus = ConvRML.fresnelZonePlateArmPaid
