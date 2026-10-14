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
-- Executed notebook blob:
--   experimental_eval/2025_03_29_sec5_experimental_MI_photon_conversion.ipynb
--   f8707b84dc696fc9218f6493467f0cda45193d3f
--
-- The notebook loads a simultaneous grayscale sweep for RML, DiffuserCam and
-- the lensed ground-truth camera, estimates per-level spatial means/standard
-- deviations, regresses variance against mean in the shot-noise regime, and
-- converts recorded intensity by
--
--   photons = clip((image - intercept) / slope, 0, infinity).
--
-- The source notebook stores full-precision slope/intercept arrays, but the
-- presently recoverable executed stdout exposes only two-decimal display
-- coefficients. We therefore pin those displayed results and do not silently
-- promote them to the hidden full-precision arrays.
------------------------------------------------------------------------

informationDesignDOI : String
informationDesignDOI = "10.1364/OPTICA.570334"

informationDesignCommit : String
informationDesignCommit = "f26873c2b58b82d84353bab2bf6edd478c5892a8"

photonConversionNotebookBlob : String
photonConversionNotebookBlob = "f8707b84dc696fc9218f6493467f0cda45193d3f"

photonCountCalibrationDriveFolder : String
photonCountCalibrationDriveFolder = "1l09Nv7POYKny0IkEAj3bgJiA-xPP33n_"

filteredSweepArchive : String
filteredSweepArchive = "1MhhUYO253RHEwmnujCmmovEVTD4z8RY8"

fullSweepArchive : String
fullSweepArchive = "1xd78nNMvNTSPJOviwL6pJ1wFwOABV7ap"

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

photonConversionFormula : String
photonConversionFormula = "clip((image - intercept) / slope, 0, infinity)"

simultaneousThreeCameraSweepPinned : Bool
simultaneousThreeCameraSweepPinned = true

sourceExecutedPhotonTransferCalibrationPaid : Bool
sourceExecutedPhotonTransferCalibrationPaid = true

detectedPhotonCountConversionPinned : Bool
detectedPhotonCountConversionPinned = true

fullPrecisionFitCoefficientsRecovered : Bool
fullPrecisionFitCoefficientsRecovered = false

opticalThroughputCalibrationPaid : Bool
opticalThroughputCalibrationPaid = false

matchedIncidentPhotonBudgetPaid : Bool
matchedIncidentPhotonBudgetPaid = false

record BerkeleyPhotonTransferCalibrationReceipt : Set where
  field
    doi : String
    sourceCommit : String
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
    fullPrecisionCoefficients : Bool
    opticalThroughputCalibration : Bool
    matchedIncidentPhotonBudget : Bool

open BerkeleyPhotonTransferCalibrationReceipt public

berkeleyPhotonTransferCalibrationReceipt : BerkeleyPhotonTransferCalibrationReceipt
berkeleyPhotonTransferCalibrationReceipt = record
  { doi = informationDesignDOI
  ; sourceCommit = informationDesignCommit
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
  ; detectedPhotonConversion = detectedPhotonCountConversionPinned
  ; fullPrecisionCoefficients = fullPrecisionFitCoefficientsRecovered
  ; opticalThroughputCalibration = opticalThroughputCalibrationPaid
  ; matchedIncidentPhotonBudget = matchedIncidentPhotonBudgetPaid
  }

-- Reuse the generic detector-channel owner rather than treating a fitted
-- photon-transfer curve as a second detector ontology. This receipt pays the
-- empirical digital-count -> estimated detected-photon conversion surface; it
-- does not pay incident-photon throughput, quantum efficiency, or equality of
-- physical photon budgets across optical encoders.
