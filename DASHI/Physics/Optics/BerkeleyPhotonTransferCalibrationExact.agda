module DASHI.Physics.Optics.BerkeleyPhotonTransferCalibrationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Optics.PhotonDetectorChannelExact as Detector

------------------------------------------------------------------------
-- BERKELEY PHOTON-TRANSFER CALIBRATION SOURCE RECEIPT
--
-- Kabuli et al., Optica 13(2), 227--235 (2026), DOI 10.1364/OPTICA.570334.
-- Code commit: f26873c2b58b82d84353bab2bf6edd478c5892a8.
-- Executed notebook:
--   experimental_eval/2025_03_29_sec5_experimental_MI_photon_conversion.ipynb
-- Git blob:
--   f8707b84dc696fc9218f6493467f0cda45193d3f
--
-- The executed notebook loads a simultaneous grayscale sweep for RML,
-- DiffuserCam and the lensed ground-truth camera, measures mean/std on declared
-- system-specific ROIs, regresses variance against mean in selected shot-noise
-- fit windows, stores slope/intercept, and converts recorded intensity by
--
--   photons = (image - intercept) / slope
--   then clips the result below at zero.
--
-- The source stdout displays rounded two-decimal coefficients. We pin exactly
-- those displayed values and do not pretend they are the hidden full-precision
-- scipy regression values. This receipt pays the source-executed detected-count
-- calibration surface. It does not pay incident-photon throughput or matched
-- incident photon budgets across distinct optical encoders.
------------------------------------------------------------------------

informationDesignDOI : String
informationDesignDOI = "10.1364/OPTICA.570334"

informationDesignCommit : String
informationDesignCommit = "f26873c2b58b82d84353bab2bf6edd478c5892a8"

photonConversionNotebookPath : String
photonConversionNotebookPath = "experimental_eval/2025_03_29_sec5_experimental_MI_photon_conversion.ipynb"

photonConversionNotebookBlob : String
photonConversionNotebookBlob = "f8707b84dc696fc9218f6493467f0cda45193d3f"

photonCountCalibrationDriveFolder : String
photonCountCalibrationDriveFolder = "1l09Nv7POYKny0IkEAj3bgJiA-xPP33n_"

filteredSweepArchive : String
filteredSweepArchive = "1MhhUYO253RHEwmnujCmmovEVTD4z8RY8"

fullSweepArchive : String
fullSweepArchive = "1xd78nNMvNTSPJOviwL6pJ1wFwOABV7ap"

------------------------------------------------------------------------
-- Exact source ROIs from the executed notebook.
------------------------------------------------------------------------

rmlROIStartY : Nat
rmlROIStartY = 500
rmlROIEndY : Nat
rmlROIEndY = 740
rmlROIStartX : Nat
rmlROIStartX = 1095
rmlROIEndX : Nat
rmlROIEndX = 1210

diffuserROIStartY : Nat
diffuserROIStartY = 410
diffuserROIEndY : Nat
diffuserROIEndY = 590
diffuserROIStartX : Nat
diffuserROIStartX = 1100
diffuserROIEndX : Nat
diffuserROIEndX = 1210

lensedROIStartY : Nat
lensedROIStartY = 500
lensedROIEndY : Nat
lensedROIEndY = 700
lensedROIStartX : Nat
lensedROIStartX = 1100
lensedROIEndX : Nat
lensedROIEndX = 1210

------------------------------------------------------------------------
-- Source-selected fit windows and displayed executed outputs.
------------------------------------------------------------------------

rmlFitStartIndex : Nat
rmlFitStartIndex = 150
rmlFitEndExclusive : Nat
rmlFitEndExclusive = 250

diffuserFitStartIndex : Nat
diffuserFitStartIndex = 150
diffuserFitEndExclusive : Nat
diffuserFitEndExclusive = 250

lensFitStartIndex : Nat
lensFitStartIndex = 175
lensFitEndExclusive : Nat
lensFitEndExclusive = 250

rmlDisplayedSlope : String
rmlDisplayedSlope = "0.02"
rmlDisplayedIntercept : String
rmlDisplayedIntercept = "1.46"

diffuserDisplayedSlope : String
diffuserDisplayedSlope = "0.03"
diffuserDisplayedIntercept : String
diffuserDisplayedIntercept = "0.36"

lensDisplayedSlope : String
lensDisplayedSlope = "0.05"
lensDisplayedIntercept : String
lensDisplayedIntercept = "0.01"

digitalToPhotonFormula : String
digitalToPhotonFormula = "(image - intercept) / slope"

photonConversionFormula : String
photonConversionFormula = "clip((image - intercept) / slope, 0, infinity)"

simultaneousThreeCameraSweepPinned : Bool
simultaneousThreeCameraSweepPinned = true

sourceExecutedPhotonTransferCalibrationPaid : Bool
sourceExecutedPhotonTransferCalibrationPaid = true

sourceDigitalToEstimatedPhotonConversionPaid : Bool
sourceDigitalToEstimatedPhotonConversionPaid = true

detectedPhotonCountConversionPinned : Bool
detectedPhotonCountConversionPinned = sourceDigitalToEstimatedPhotonConversionPaid

fullPrecisionFitCoefficientsRecovered : Bool
fullPrecisionFitCoefficientsRecovered = false

-- The raw multi-gigabyte grayscale sweep was not re-executed in the current
-- runtime; source execution and local raw-data re-execution are distinct.
localRawCalibrationSweepReexecuted : Bool
localRawCalibrationSweepReexecuted = false

-- A detector DN->estimated detected-photon calibration is not an optical
-- incident-photon throughput calibration. Encoder transmission / collection /
-- QE system accounting remains independently required for matched input flux.
incidentPhotonThroughputCalibrationPaid : Bool
incidentPhotonThroughputCalibrationPaid = false
opticalThroughputCalibrationPaid : Bool
opticalThroughputCalibrationPaid = incidentPhotonThroughputCalibrationPaid

matchedPhysicalPhotonBudgetPaid : Bool
matchedPhysicalPhotonBudgetPaid = false
matchedIncidentPhotonBudgetPaid : Bool
matchedIncidentPhotonBudgetPaid = matchedPhysicalPhotonBudgetPaid

record BerkeleyPhotonTransferCalibrationReceipt : Set where
  field
    doi : String
    sourceCommit : String
    notebookPath : String
    notebookBlob : String
    calibrationDriveFolder : String
    filteredCalibrationArchive : String
    fullCalibrationArchive : String
    rmlSlopeDisplayed : String
    rmlInterceptDisplayed : String
    diffuserSlopeDisplayed : String
    diffuserInterceptDisplayed : String
    lensSlopeDisplayed : String
    lensInterceptDisplayed : String
    conversion : String
    simultaneousSweep : Bool
    sourceExecutedCalibration : Bool
    detectedPhotonConversion : Bool
    localRawSweepReexecuted : Bool
    fullPrecisionCoefficients : Bool
    incidentPhotonThroughputCalibration : Bool
    matchedPhysicalPhotonBudget : Bool

open BerkeleyPhotonTransferCalibrationReceipt public

berkeleyPhotonTransferCalibrationReceipt : BerkeleyPhotonTransferCalibrationReceipt
berkeleyPhotonTransferCalibrationReceipt = record
  { doi = informationDesignDOI
  ; sourceCommit = informationDesignCommit
  ; notebookPath = photonConversionNotebookPath
  ; notebookBlob = photonConversionNotebookBlob
  ; calibrationDriveFolder = photonCountCalibrationDriveFolder
  ; filteredCalibrationArchive = filteredSweepArchive
  ; fullCalibrationArchive = fullSweepArchive
  ; rmlSlopeDisplayed = rmlDisplayedSlope
  ; rmlInterceptDisplayed = rmlDisplayedIntercept
  ; diffuserSlopeDisplayed = diffuserDisplayedSlope
  ; diffuserInterceptDisplayed = diffuserDisplayedIntercept
  ; lensSlopeDisplayed = lensDisplayedSlope
  ; lensInterceptDisplayed = lensDisplayedIntercept
  ; conversion = photonConversionFormula
  ; simultaneousSweep = simultaneousThreeCameraSweepPinned
  ; sourceExecutedCalibration = sourceExecutedPhotonTransferCalibrationPaid
  ; detectedPhotonConversion = sourceDigitalToEstimatedPhotonConversionPaid
  ; localRawSweepReexecuted = localRawCalibrationSweepReexecuted
  ; fullPrecisionCoefficients = fullPrecisionFitCoefficientsRecovered
  ; incidentPhotonThroughputCalibration = incidentPhotonThroughputCalibrationPaid
  ; matchedPhysicalPhotonBudget = matchedPhysicalPhotonBudgetPaid
  }

-- Reuse the generic detector-channel owner rather than treating a fitted
-- photon-transfer curve as a second detector ontology. The source calibration
-- pays an empirical digital-count -> estimated detected-photon observation
-- transform. It does not identify incident photons before the encoder or prove
-- equal photon budgets across distinct optical systems.
