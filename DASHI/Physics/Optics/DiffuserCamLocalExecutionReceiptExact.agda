module DASHI.Physics.Optics.DiffuserCamLocalExecutionReceiptExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LOCAL EXECUTION RECEIPTS — 2026-10-12
--
-- These receipts were produced by executing the branch's source-H numerical
-- logic locally. They certify implementation identities / finite randomized
-- checks and claim-scale memory planning only. They do NOT substitute for an
-- execution on Waller's pinned `example_psfs.mat`, and they do not establish
-- physical photon calibration.
------------------------------------------------------------------------

syntheticReceiptPath : String
syntheticReceiptPath = "receipts/optics/waller_diffusercam_synthetic_receipt.json"

syntheticReceiptSHA256 : String
syntheticReceiptSHA256 = "420c774dd539760142378e4832823e339a6aed5dad50c269be94af7a857d1d17"

claimScaleReceiptPath : String
claimScaleReceiptPath = "receipts/optics/waller_diffusercam_claim_scale_receipt.json"

claimScaleReceiptSHA256 : String
claimScaleReceiptSHA256 = "37e6225ac91672578a6a8bb4c7bd29c8d54b76450f6b1a0209aa1b02e0570ebb"

syntheticSeed : Nat
syntheticSeed = 1729

syntheticShapesChecked : Nat
syntheticShapesChecked = 4

gershgorinSupportsChecked : Nat
gershgorinSupportsChecked = 500

gershgorinBoundViolations : Nat
gershgorinBoundViolations = 0

maxFFTvsRollAbsError : String
maxFFTvsRollAbsError = "1.1102230246251565e-16"

worstObservedMinusBoundMargin : String
worstObservedMinusBoundMargin = "-4.440892098500626e-16"

claimScaleBudgetBytes : Nat
claimScaleBudgetBytes = 200000000

claimScaleLargestSafeSyntheticRadius : Nat
claimScaleLargestSafeSyntheticRadius = 2

syntheticOperatorReceiptCaptured : Bool
syntheticOperatorReceiptCaptured = true

claimScalePlannerReceiptCaptured : Bool
claimScalePlannerReceiptCaptured = true

realBerkeleyPSFReceiptCaptured : Bool
realBerkeleyPSFReceiptCaptured = false

physicalPhotonCalibrationReceiptCaptured : Bool
physicalPhotonCalibrationReceiptCaptured = false

record DiffuserCamLocalExecutionReceipt : Set where
  field
    operatorReceiptPath : String
    operatorReceiptHash : String
    plannerReceiptPath : String
    plannerReceiptHash : String
    shapesChecked : Nat
    supportsChecked : Nat
    violations : Nat
    maxFFTError : String
    worstBoundMargin : String
    memoryBudgetBytes : Nat
    largestSafeSyntheticRadius : Nat
    syntheticOperatorReceipt : Bool
    claimScalePlannerReceipt : Bool
    realPSFReceipt : Bool
    physicalPhotonReceipt : Bool

open DiffuserCamLocalExecutionReceipt public

currentDiffuserCamLocalExecutionReceipt : DiffuserCamLocalExecutionReceipt
currentDiffuserCamLocalExecutionReceipt = record
  { operatorReceiptPath = syntheticReceiptPath
  ; operatorReceiptHash = syntheticReceiptSHA256
  ; plannerReceiptPath = claimScaleReceiptPath
  ; plannerReceiptHash = claimScaleReceiptSHA256
  ; shapesChecked = syntheticShapesChecked
  ; supportsChecked = gershgorinSupportsChecked
  ; violations = gershgorinBoundViolations
  ; maxFFTError = maxFFTvsRollAbsError
  ; worstBoundMargin = worstObservedMinusBoundMargin
  ; memoryBudgetBytes = claimScaleBudgetBytes
  ; largestSafeSyntheticRadius = claimScaleLargestSafeSyntheticRadius
  ; syntheticOperatorReceipt = syntheticOperatorReceiptCaptured
  ; claimScalePlannerReceipt = claimScalePlannerReceiptCaptured
  ; realPSFReceipt = realBerkeleyPSFReceiptCaptured
  ; physicalPhotonReceipt = physicalPhotonCalibrationReceiptCaptured
  }
