module DASHI.Physics.Optics.BerkeleySystemCharacterizationDetectedPhotonExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Optics.BerkeleyPhotonTransferCalibrationExact as PhotonTransfer

------------------------------------------------------------------------
-- REAL PLD SYSTEM-CHARACTERIZATION DETECTED-PHOTON RECEIPT
--
-- Public Drive `System Characterization` archives were materialised locally:
--   RML      1mHJp99Twe0nSL3_HbNXjXjmV9zDy3YvI
--   Diffuser 1-0rpd6gHgjdFshVMl6Gw1M0NqAliechM
-- Each contains 15 matched 1920x1200 grayscale TIFF point-source positions.
-- Applying the source-executed displayed photon-transfer fits gives a real-data
-- detected-photon characterization. TIFF metadata contains no exposure field;
-- therefore raw count ratios are not promoted to exposure-normalized throughput
-- or matched incident-photon budgets.
------------------------------------------------------------------------

systemCharacterizationDriveFolder : String
systemCharacterizationDriveFolder = "1nr1pUrg80JQm8WyLa6wvFktmJ_pniOio"

rmlArchiveDriveID : String
rmlArchiveDriveID = "1mHJp99Twe0nSL3_HbNXjXjmV9zDy3YvI"
rmlArchiveSHA256 : String
rmlArchiveSHA256 = "0f7f1f92c57476dba5e5033ebcbc5392084c93dfd3b0c7edf4e125dad10ee155"

diffuserArchiveDriveID : String
diffuserArchiveDriveID = "1-0rpd6gHgjdFshVMl6Gw1M0NqAliechM"
diffuserArchiveSHA256 : String
diffuserArchiveSHA256 = "d9466f0ebc3d8f2633adefc9c4dec909dff4b3388fc2006726621f40f63b4a57"

receiptPath : String
receiptPath = "receipts/optics/berkeley_system_characterization_detected_photon_receipt.json"
receiptGitBlobSHA : String
receiptGitBlobSHA = "f7f6d2e1fda18d8ef87a1b90a0af1be785f3b1cb"
executionScript : String
executionScript = "scripts/check_berkeley_system_characterization_detected_photons.py"

matchedCharacterizationPositions : Nat
matchedCharacterizationPositions = 15

rawDetectedCountRatioMin : String
rawDetectedCountRatioMin = "0.02211386329642063"
rawDetectedCountRatioMedian : String
rawDetectedCountRatioMedian = "0.058673780183631376"
rawDetectedCountRatioMean : String
rawDetectedCountRatioMean = "0.06388591944326388"
rawDetectedCountRatioMax : String
rawDetectedCountRatioMax = "0.1317059368412121"

realMeasuredTIFFsExecuted : Bool
realMeasuredTIFFsExecuted = true

detectedPhotonCharacterizationPaid : Bool
detectedPhotonCharacterizationPaid = true

characterizationExposureMetadataRecovered : Bool
characterizationExposureMetadataRecovered = false

exposureNormalizedResponsePaid : Bool
exposureNormalizedResponsePaid = false

incidentThroughputPaid : Bool
incidentThroughputPaid = false

matchedIncidentPhotonBudgetPaid : Bool
matchedIncidentPhotonBudgetPaid = false

record BerkeleySystemCharacterizationDetectedPhotonReceipt : Set where
  field
    driveFolder : String
    rmlArchive : String
    diffuserArchive : String
    receiptBlob : String
    positions : Nat
    measuredTIFFsExecuted : Bool
    detectedPhotonCharacterization : Bool
    exposureMetadata : Bool
    exposureNormalizedResponse : Bool
    incidentThroughput : Bool
    matchedIncidentPhotonBudget : Bool

open BerkeleySystemCharacterizationDetectedPhotonReceipt public

currentBerkeleySystemCharacterizationDetectedPhotonReceipt :
  BerkeleySystemCharacterizationDetectedPhotonReceipt
currentBerkeleySystemCharacterizationDetectedPhotonReceipt = record
  { driveFolder = systemCharacterizationDriveFolder
  ; rmlArchive = rmlArchiveDriveID
  ; diffuserArchive = diffuserArchiveDriveID
  ; receiptBlob = receiptGitBlobSHA
  ; positions = matchedCharacterizationPositions
  ; measuredTIFFsExecuted = realMeasuredTIFFsExecuted
  ; detectedPhotonCharacterization = detectedPhotonCharacterizationPaid
  ; exposureMetadata = characterizationExposureMetadataRecovered
  ; exposureNormalizedResponse = exposureNormalizedResponsePaid
  ; incidentThroughput = incidentThroughputPaid
  ; matchedIncidentPhotonBudget = matchedIncidentPhotonBudgetPaid
  }

-- PhotonTransfer supplies the empirical DN -> estimated detected-photon map.
-- This owner supplies real measured characterization bytes and execution, but
-- deliberately refuses the next throughput promotion without exposure/source
-- normalization for the same characterization captures.
