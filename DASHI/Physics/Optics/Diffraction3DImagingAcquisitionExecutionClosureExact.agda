module DASHI.Physics.Optics.Diffraction3DImagingAcquisitionExecutionClosureExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Optics.Diffraction3DImagingAcquisitionMaxCutExact as Base
import DASHI.Physics.Optics.BerkeleyPhotonTransferCalibrationExact as Photon
import DASHI.Physics.Optics.BerkeleyPhotonTransferStimulusExecutionExact as Stimulus
import DASHI.Physics.Optics.BerkeleySystemCharacterizationDetectedPhotonExact as Characterization
import DASHI.Physics.Optics.BerkeleyPLD100kReleaseProvenanceExact as PLD100k
import DASHI.Physics.Optics.BerkeleyPLDArchiveRunMetadataBoundaryExact as ArchiveRun
import DASHI.Physics.Optics.BerkeleyDiffuserCamPublicCalibrationExact as DiffuserCalibration
import DASHI.Physics.Optics.BerkeleyDiffuserCamDepthConditioningExact as Conditioning

------------------------------------------------------------------------
-- TERMINAL EXECUTION / ACQUISITION CLOSURE
--
-- This owner records the strongest current optics cut after actual local/public
-- data execution. It is intentionally thin over the existing owners.
--
-- PAID:
--   * exact DiffuserCam source-H/compiler + synthetic exhaustive execution;
--   * exact pinned Waller example_psfs.mat bytes executed through the real
--     same-H depth + radius-1 translated-column audit;
--   * finite k=1 same-H Gershgorin/gain/restricted-kappa receipt;
--   * real PSF claim-scale planner through first unsafe radius under 5 GiB;
--   * live public 0..255 photon-transfer stimulus bytes executed locally;
--   * source-executed DN -> estimated detected-photon calibration;
--   * real public RML/diffuser system-characterization TIFFs executed through
--     that calibration;
--   * publication-level synchronized 100k PLD provenance + 80/50/4 ms exposure
--     identity;
--   * exact released 100k archive coordinates and release-code lineage.
--
-- PINNED BUT NOT DECODED IN THIS RUNTIME:
--   * source-saved full-precision slope/intercept npy blobs.
--
-- GENUINE REMAINING PHYSICAL / EXECUTION LEAVES:
--   P2: recover a same-run archive metadata.json (or equivalent run manifest)
--       tying released PLD bytes to exposure configuration;
--   P3: recover/measure same-object incident/source normalization and optical
--       throughput needed for a matched incident-photon comparison;
--   K1: exact-head Agda/kernel execution.
--
-- The finite radius-1 receipt is not an all-resolution RIP theorem. Optional
-- FZP comparison remains downstream and is not a blocker.
------------------------------------------------------------------------

rmlFullPrecisionFitBlob : String
rmlFullPrecisionFitBlob = "d40f1bc386d3b398a50d06ec2ffd6e67b80c94b5"

diffuserFullPrecisionFitBlob : String
diffuserFullPrecisionFitBlob = "9b6a66d4168f9e81102ac3666c13fe90eed30a81"

lensedFullPrecisionFitBlob : String
lensedFullPrecisionFitBlob = "b2877bbd9c90dc26c12b3b9552e9e345a1ed46a9"

fullPrecisionFitArtifactsPinned : Bool
fullPrecisionFitArtifactsPinned = true

fullPrecisionFitValuesDecoded : Bool
fullPrecisionFitValuesDecoded = false

livePhotonStimulusExecuted : Bool
livePhotonStimulusExecuted = Stimulus.localStimulusBytesExecuted

detectedPhotonCalibrationPaid : Bool
detectedPhotonCalibrationPaid = Photon.detectedPhotonCountConversionPinned

realCharacterizationDetectedPhotonPaid : Bool
realCharacterizationDetectedPhotonPaid = Characterization.detectedPhotonCharacterizationPaid

published100kAcquisitionPaid : Bool
published100kAcquisitionPaid = PLD100k.published100kAcquisitionProvenancePaid

published100kExposurePaid : Bool
published100kExposurePaid = PLD100k.published100kExposureIdentityPaid

realDiffuserPSFReceiptPaid : Bool
realDiffuserPSFReceiptPaid = Conditioning.depthOnlyNumericalReceiptCaptured

archiveRunMetadataRecovered : Bool
archiveRunMetadataRecovered = ArchiveRun.exactArchiveRunLogRecovered

archiveSameRunExposurePaid : Bool
archiveSameRunExposurePaid = ArchiveRun.exactArchiveExposureSameRunPaid

characterizationExposureNormalizedPaid : Bool
characterizationExposureNormalizedPaid = Characterization.exposureNormalizedResponsePaid

incidentPhotonThroughputPaid : Bool
incidentPhotonThroughputPaid = Characterization.incidentThroughputPaid

matchedIncidentPhotonBudgetPaid : Bool
matchedIncidentPhotonBudgetPaid = Characterization.matchedIncidentPhotonBudgetPaid

agdaKernelPaid : Bool
agdaKernelPaid = Base.agdaKernelReceiptCaptured

record Diffraction3DImagingAcquisitionExecutionClosure : Set where
  field
    sourceHArchitecture : Bool
    stimulusExecution : Bool
    detectedPhotonCalibration : Bool
    realCharacterizationDetectedPhotons : Bool
    publication100kProvenance : Bool
    publication100kExposure : Bool
    fullPrecisionFitArtifacts : Bool
    fullPrecisionFitDecoded : Bool
    realPSFExecution : Bool
    archiveRunManifest : Bool
    archiveSameRunExposure : Bool
    exposureNormalizedCharacterization : Bool
    incidentPhotonThroughput : Bool
    matchedIncidentPhotonBudget : Bool
    kernelReceipt : Bool

open Diffraction3DImagingAcquisitionExecutionClosure public

currentDiffraction3DImagingAcquisitionExecutionClosure :
  Diffraction3DImagingAcquisitionExecutionClosure
currentDiffraction3DImagingAcquisitionExecutionClosure = record
  { sourceHArchitecture = Base.sourceOperatorSelectedGridColumnCompilerPaid
  ; stimulusExecution = livePhotonStimulusExecuted
  ; detectedPhotonCalibration = detectedPhotonCalibrationPaid
  ; realCharacterizationDetectedPhotons = realCharacterizationDetectedPhotonPaid
  ; publication100kProvenance = published100kAcquisitionPaid
  ; publication100kExposure = published100kExposurePaid
  ; fullPrecisionFitArtifacts = fullPrecisionFitArtifactsPinned
  ; fullPrecisionFitDecoded = fullPrecisionFitValuesDecoded
  ; realPSFExecution = realDiffuserPSFReceiptPaid
  ; archiveRunManifest = archiveRunMetadataRecovered
  ; archiveSameRunExposure = archiveSameRunExposurePaid
  ; exposureNormalizedCharacterization = characterizationExposureNormalizedPaid
  ; incidentPhotonThroughput = incidentPhotonThroughputPaid
  ; matchedIncidentPhotonBudget = matchedIncidentPhotonBudgetPaid
  ; kernelReceipt = agdaKernelPaid
  }

realPSFArtifactIdentityPinned : Bool
realPSFArtifactIdentityPinned = DiffuserCalibration.publicCalibrationArtifactPinned
