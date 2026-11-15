module DASHI.Physics.Optics.BerkeleyDiffuserCamPublicCalibrationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE / ARTIFACT RECEIPT
--
-- This owner pins the public Waller-Lab DiffuserCam demo calibration
-- artifact. Pinning repository objects proves provenance/identity only; it
-- does not decode the MATLAB binary, prove physical calibration, or manufacture
-- a quantitative inverse theorem.
------------------------------------------------------------------------

diffuserCamRepository : String
diffuserCamRepository = "Waller-Lab/DiffuserCam"

diffuserCamCommit : String
diffuserCamCommit = "c8516cb8f482c2bb15e75ebebd91a74b88732c95"

examplePSFPath : String
examplePSFPath = "example_data/example_psfs.mat"

examplePSFBlobSHA : String
examplePSFBlobSHA = "db59065bdaf44fe771a6d3fbe22ae3c703527b5f"

examplePSFBytes : Nat
examplePSFBytes = 10823885

examplePSFVariable : String
examplePSFVariable = "psf"

exampleRawPath : String
exampleRawPath = "example_data/example_raw.png"

exampleRawBlobSHA : String
exampleRawBlobSHA = "3b4c3b2ca674bbd21d925a1f0a1ea79a77efe5df"

exampleRawBytes : Nat
exampleRawBytes = 122698

publicCalibrationArtifactPinned : Bool
publicCalibrationArtifactPinned = true

publicRawMeasurementArtifactPinned : Bool
publicRawMeasurementArtifactPinned = true

-- The connector can identify the binary artifact but does not expose its
-- MATLAB array payload as UTF-8. Keep numerical ingestion fail-closed.
numericPSFArrayIngested : Bool
numericPSFArrayIngested = false

record BerkeleyDiffuserCamPublicCalibrationReceipt : Set where
  field
    repository : String
    commit : String
    psfPath : String
    psfBlobSHA : String
    psfBytes : Nat
    psfVariable : String
    rawMeasurementPath : String
    rawMeasurementBlobSHA : String
    rawMeasurementBytes : Nat
    artifactIdentityPaid : Bool
    rawArtifactIdentityPaid : Bool
    decodedNumericPSFPaid : Bool

open BerkeleyDiffuserCamPublicCalibrationReceipt public

publicDiffuserCamCalibrationReceipt : BerkeleyDiffuserCamPublicCalibrationReceipt
publicDiffuserCamCalibrationReceipt = record
  { repository = diffuserCamRepository
  ; commit = diffuserCamCommit
  ; psfPath = examplePSFPath
  ; psfBlobSHA = examplePSFBlobSHA
  ; psfBytes = examplePSFBytes
  ; psfVariable = examplePSFVariable
  ; rawMeasurementPath = exampleRawPath
  ; rawMeasurementBlobSHA = exampleRawBlobSHA
  ; rawMeasurementBytes = exampleRawBytes
  ; artifactIdentityPaid = publicCalibrationArtifactPinned
  ; rawArtifactIdentityPaid = publicRawMeasurementArtifactPinned
  ; decodedNumericPSFPaid = numericPSFArrayIngested
  }
