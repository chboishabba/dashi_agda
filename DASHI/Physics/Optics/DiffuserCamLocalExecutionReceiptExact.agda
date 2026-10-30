module DASHI.Physics.Optics.DiffuserCamLocalExecutionReceiptExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LOCAL EXECUTION RECEIPTS — 2026-10-12
--
-- These receipts were produced by executing the branch's source-H numerical
-- logic locally. They certify implementation identities, an exhaustive finite
-- support-order check on declared synthetic fixtures, claim-scale memory
-- planning, and a focused receipt-contract pytest. They do NOT substitute for
-- execution on Waller's pinned `example_psfs.mat`, full-repository pytest, or
-- Agda kernel checking, and they do not establish physical photon calibration.
------------------------------------------------------------------------

syntheticReceiptPath : String
syntheticReceiptPath = "receipts/optics/waller_diffusercam_synthetic_receipt.json"

syntheticReceiptGitBlobSHA : String
syntheticReceiptGitBlobSHA = "128d24378b12a055282ffccb813744e626b846e1"

claimScaleReceiptPath : String
claimScaleReceiptPath = "receipts/optics/waller_diffusercam_claim_scale_receipt.json"

claimScaleReceiptGitBlobSHA : String
claimScaleReceiptGitBlobSHA = "52cecec7a7b61fc5577129e9b704ee53482f2c82"

focusedPytestReceiptPath : String
focusedPytestReceiptPath = "receipts/optics/waller_diffusercam_local_pytest_receipt.json"

focusedPytestReceiptGitBlobSHA : String
focusedPytestReceiptGitBlobSHA = "5be367654d6a6510a05cc81d83e4c84af89e465f"

syntheticSeed : Nat
syntheticSeed = 1729

syntheticShapesChecked : Nat
syntheticShapesChecked = 4

exhaustiveSupportOrderMaximum : Nat
exhaustiveSupportOrderMaximum = 3

gershgorinSupportsChecked : Nat
gershgorinSupportsChecked = 22218

gershgorinBoundViolations : Nat
gershgorinBoundViolations = 0

maxFFTvsRollAbsError : String
maxFFTvsRollAbsError = "1.6653345369377348e-16"

worstObservedMinusBoundMargin : String
worstObservedMinusBoundMargin = "-4.440892098500626e-16"

claimScaleBudgetBytes : Nat
claimScaleBudgetBytes = 200000000

claimScaleLargestSafeSyntheticRadius : Nat
claimScaleLargestSafeSyntheticRadius = 2

focusedPytestTestsPassed : Nat
focusedPytestTestsPassed = 2

focusedPytestTestsFailed : Nat
focusedPytestTestsFailed = 0

syntheticOperatorReceiptCaptured : Bool
syntheticOperatorReceiptCaptured = true

exhaustiveFiniteSupportReceiptCaptured : Bool
exhaustiveFiniteSupportReceiptCaptured = true

claimScalePlannerReceiptCaptured : Bool
claimScalePlannerReceiptCaptured = true

focusedReceiptContractPytestCaptured : Bool
focusedReceiptContractPytestCaptured = true

fullRepositoryPytestCaptured : Bool
fullRepositoryPytestCaptured = false

agdaKernelReceiptCaptured : Bool
agdaKernelReceiptCaptured = false

realBerkeleyPSFReceiptCaptured : Bool
realBerkeleyPSFReceiptCaptured = false

physicalPhotonCalibrationReceiptCaptured : Bool
physicalPhotonCalibrationReceiptCaptured = false

record DiffuserCamLocalExecutionReceipt : Set where
  field
    operatorReceiptPath : String
    operatorReceiptBlob : String
    plannerReceiptPath : String
    plannerReceiptBlob : String
    pytestReceiptPath : String
    pytestReceiptBlob : String
    shapesChecked : Nat
    exhaustiveOrderMaximum : Nat
    supportsChecked : Nat
    violations : Nat
    maxFFTError : String
    worstBoundMargin : String
    memoryBudgetBytes : Nat
    largestSafeSyntheticRadius : Nat
    pytestPassed : Nat
    pytestFailed : Nat
    syntheticOperatorReceipt : Bool
    exhaustiveSupportReceipt : Bool
    claimScalePlannerReceipt : Bool
    focusedPytestReceipt : Bool
    fullRepoPytestReceipt : Bool
    kernelReceipt : Bool
    realPSFReceipt : Bool
    physicalPhotonReceipt : Bool

open DiffuserCamLocalExecutionReceipt public

currentDiffuserCamLocalExecutionReceipt : DiffuserCamLocalExecutionReceipt
currentDiffuserCamLocalExecutionReceipt = record
  { operatorReceiptPath = syntheticReceiptPath
  ; operatorReceiptBlob = syntheticReceiptGitBlobSHA
  ; plannerReceiptPath = claimScaleReceiptPath
  ; plannerReceiptBlob = claimScaleReceiptGitBlobSHA
  ; pytestReceiptPath = focusedPytestReceiptPath
  ; pytestReceiptBlob = focusedPytestReceiptGitBlobSHA
  ; shapesChecked = syntheticShapesChecked
  ; exhaustiveOrderMaximum = exhaustiveSupportOrderMaximum
  ; supportsChecked = gershgorinSupportsChecked
  ; violations = gershgorinBoundViolations
  ; maxFFTError = maxFFTvsRollAbsError
  ; worstBoundMargin = worstObservedMinusBoundMargin
  ; memoryBudgetBytes = claimScaleBudgetBytes
  ; largestSafeSyntheticRadius = claimScaleLargestSafeSyntheticRadius
  ; pytestPassed = focusedPytestTestsPassed
  ; pytestFailed = focusedPytestTestsFailed
  ; syntheticOperatorReceipt = syntheticOperatorReceiptCaptured
  ; exhaustiveSupportReceipt = exhaustiveFiniteSupportReceiptCaptured
  ; claimScalePlannerReceipt = claimScalePlannerReceiptCaptured
  ; focusedPytestReceipt = focusedReceiptContractPytestCaptured
  ; fullRepoPytestReceipt = fullRepositoryPytestCaptured
  ; kernelReceipt = agdaKernelReceiptCaptured
  ; realPSFReceipt = realBerkeleyPSFReceiptCaptured
  ; physicalPhotonReceipt = physicalPhotonCalibrationReceiptCaptured
  }
