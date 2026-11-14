module DASHI.Physics.Optics.BerkeleyPhotonTransferLocalExecutionReceiptExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Optics.BerkeleyPhotonTransferCalibrationExact as Source

------------------------------------------------------------------------
-- LOCAL PHOTON-TRANSFER COMPILER EXECUTION RECEIPT
--
-- Deterministic local Poisson fixtures validate the algebraic compiler shape
-- used by the source-executed Berkeley notebook:
--
--   photons ~ Poisson(lambda)
--   digital = slope * photons + intercept
--   Var[digital] ~ slope * E[digital] + constant
--   recovered photons = (digital - intercept) / slope.
--
-- This is a compiler/numerical-sanity receipt. It is not a re-execution of the
-- multi-GB Berkeley grayscale sweep and not an incident-throughput calibration.
------------------------------------------------------------------------

receiptPath : String
receiptPath = "receipts/optics/berkeley_photon_transfer_synthetic_receipt.json"

receiptGitBlobSHA : String
receiptGitBlobSHA = "f556ac6a00d74961fdfccb2547426802818348ce"

executionScript : String
executionScript = "scripts/check_berkeley_photon_transfer_calibration.py"

executionSeed : Nat
executionSeed = 1729

rmlFitSlope : String
rmlFitSlope = "0.020283732448944863"
rmlRelativeSlopeError : String
rmlRelativeSlopeError = "0.014186622447243113"

diffuserFitSlope : String
diffuserFitSlope = "0.03081412628239992"
diffuserRelativeSlopeError : String
diffuserRelativeSlopeError = "0.027137542746664044"

lensedFitSlope : String
lensedFitSlope = "0.05145730875283487"
lensedRelativeSlopeError : String
lensedRelativeSlopeError = "0.029146175056697365"

maxInverseAbsoluteError : String
maxInverseAbsoluteError = "1.1368683772161603e-13"

localSyntheticPhotonTransferReceiptCaptured : Bool
localSyntheticPhotonTransferReceiptCaptured = true

rawBerkeleySweepReexecuted : Bool
rawBerkeleySweepReexecuted = false

sourceExecutedNotebookReproducedFromRawData : Bool
sourceExecutedNotebookReproducedFromRawData = false

incidentThroughputCalibrationPaid : Bool
incidentThroughputCalibrationPaid = false

matchedPhysicalPhotonBudgetPaid : Bool
matchedPhysicalPhotonBudgetPaid = false

record BerkeleyPhotonTransferLocalExecutionReceipt : Set where
  field
    path : String
    blob : String
    script : String
    seed : Nat
    rmlSlope : String
    diffuserSlope : String
    lensedSlope : String
    inverseError : String
    localSyntheticReceipt : Bool
    rawSweepReexecuted : Bool
    sourceRawReproduction : Bool
    incidentThroughput : Bool
    matchedPhysicalPhotonBudget : Bool

open BerkeleyPhotonTransferLocalExecutionReceipt public

currentBerkeleyPhotonTransferLocalExecutionReceipt :
  BerkeleyPhotonTransferLocalExecutionReceipt
currentBerkeleyPhotonTransferLocalExecutionReceipt = record
  { path = receiptPath
  ; blob = receiptGitBlobSHA
  ; script = executionScript
  ; seed = executionSeed
  ; rmlSlope = rmlFitSlope
  ; diffuserSlope = diffuserFitSlope
  ; lensedSlope = lensedFitSlope
  ; inverseError = maxInverseAbsoluteError
  ; localSyntheticReceipt = localSyntheticPhotonTransferReceiptCaptured
  ; rawSweepReexecuted = rawBerkeleySweepReexecuted
  ; sourceRawReproduction = sourceExecutedNotebookReproducedFromRawData
  ; incidentThroughput = incidentThroughputCalibrationPaid
  ; matchedPhysicalPhotonBudget = matchedPhysicalPhotonBudgetPaid
  }

-- Importing Source binds this local compiler check to the actual Berkeley source
-- calibration owner rather than creating a competing detector interpretation.
