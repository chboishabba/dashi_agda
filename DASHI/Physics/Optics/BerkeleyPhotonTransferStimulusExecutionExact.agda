module DASHI.Physics.Optics.BerkeleyPhotonTransferStimulusExecutionExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Optics.BerkeleyPhotonTransferCalibrationExact as Calibration

------------------------------------------------------------------------
-- PUBLIC PHOTON-TRANSFER STIMULUS EXECUTION / PROVENANCE CORRECTION
--
-- The public Photon Count Calibration Drive folder currently exposes:
--   grayscale_sweep.zip      5,234,047,530 bytes (three-camera responses)
--   grayscale_imgs_500.zip         278,877 bytes (display stimuli)
--
-- The previously recorded `filteredSweepArchive` id in Calibration no longer
-- resolves through Drive.  We do not silently rewrite that historical source
-- record.  This owner records the live artifact identity and a local execution
-- receipt over its bytes.
--
-- Local execution verified that grayscale_imgs_500.zip contains exactly 256
-- real stimulus PNGs, each 500x500 uint8 and spatially constant, with one image
-- at each integer level 0..255.  This pays stimulus integrity only; it does not
-- re-execute the 5.23 GB three-camera response sweep.
------------------------------------------------------------------------

photonCountCalibrationDriveFolder : String
photonCountCalibrationDriveFolder = "1l09Nv7POYKny0IkEAj3bgJiA-xPP33n_"

liveStimulusArchiveDriveID : String
liveStimulusArchiveDriveID = "1MhhavOO3NUroXiiwgVcX8wJS_4mJgz9T"

liveStimulusArchiveName : String
liveStimulusArchiveName = "grayscale_imgs_500.zip"

liveStimulusArchiveBytes : Nat
liveStimulusArchiveBytes = 278877

liveStimulusArchiveSHA256 : String
liveStimulusArchiveSHA256 = "51b5c10d4fa5a3797185ba48bf88f2d7573725a13c378b7e0025d61a93979765"

fullResponseSweepDriveID : String
fullResponseSweepDriveID = "1xd78nNMvNTSPJOviwL6pJ1wFwOABV7ap"

fullResponseSweepBytes : String
fullResponseSweepBytes = "5234047530"

localReceiptPath : String
localReceiptPath = "receipts/optics/berkeley_photon_transfer_stimulus_receipt.json"

localReceiptGitBlobSHA : String
localReceiptGitBlobSHA = "a1319262bb3f7aa69ecba9af18c2e7b704122560"

stimulusImageCount : Nat
stimulusImageCount = 256

stimulusWidth : Nat
stimulusWidth = 500

stimulusHeight : Nat
stimulusHeight = 500

stimulusMinimumLevel : Nat
stimulusMinimumLevel = 0

stimulusMaximumLevel : Nat
stimulusMaximumLevel = 255

legacyFilteredSweepIDCurrentlyResolvable : Bool
legacyFilteredSweepIDCurrentlyResolvable = false

liveStimulusArtifactPinned : Bool
liveStimulusArtifactPinned = true

localStimulusBytesExecuted : Bool
localStimulusBytesExecuted = true

allStimulusImagesConstantAndLevelExact : Bool
allStimulusImagesConstantAndLevelExact = true

fullResponseSweepLocallyReexecuted : Bool
fullResponseSweepLocallyReexecuted = false

incidentPhotonThroughputPaid : Bool
incidentPhotonThroughputPaid = false

record BerkeleyPhotonTransferStimulusExecutionReceipt : Set where
  field
    driveFolder : String
    stimulusArchive : String
    stimulusSHA256 : String
    responseSweep : String
    receiptBlob : String
    images : Nat
    width : Nat
    height : Nat
    legacyIDResolvable : Bool
    stimulusPinned : Bool
    stimulusExecuted : Bool
    constantLevelExact : Bool
    rawResponseSweepReexecuted : Bool
    incidentThroughput : Bool

open BerkeleyPhotonTransferStimulusExecutionReceipt public

currentBerkeleyPhotonTransferStimulusExecutionReceipt :
  BerkeleyPhotonTransferStimulusExecutionReceipt
currentBerkeleyPhotonTransferStimulusExecutionReceipt = record
  { driveFolder = photonCountCalibrationDriveFolder
  ; stimulusArchive = liveStimulusArchiveDriveID
  ; stimulusSHA256 = liveStimulusArchiveSHA256
  ; responseSweep = fullResponseSweepDriveID
  ; receiptBlob = localReceiptGitBlobSHA
  ; images = stimulusImageCount
  ; width = stimulusWidth
  ; height = stimulusHeight
  ; legacyIDResolvable = legacyFilteredSweepIDCurrentlyResolvable
  ; stimulusPinned = liveStimulusArtifactPinned
  ; stimulusExecuted = localStimulusBytesExecuted
  ; constantLevelExact = allStimulusImagesConstantAndLevelExact
  ; rawResponseSweepReexecuted = fullResponseSweepLocallyReexecuted
  ; incidentThroughput = incidentPhotonThroughputPaid
  }

-- Calibration remains the source authority for the notebook regression and
-- digital-count -> estimated detected-photon conversion.  This owner only
-- repairs the live external artifact coordinate and records local stimulus-byte
-- execution; it does not promote source stimuli into camera-response evidence.
