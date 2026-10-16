module DASHI.Mathematics.CrossPollination.EisensteinJZeroPointCMLeanReceiptExact where

------------------------------------------------------------------------
-- LEAN j=0 ELLIPTIC POINT-GROUP / LOCAL-EULER CROSS-PROVER RECEIPT
--
-- Repository-internal provenance only.  This does not import a Lean proof term
-- into Agda and does not promote source-written Lean to Agda kernel authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Interop.Round11MachinCrossProverRecognitionExact as Attribution

record LeanJZeroCMFormalSourceReceipt : Set where
  constructor lean-jzero-cm-formal-source-receipt
  field
    repository : String
    pullRequest : String
    branch : String
    commit : String
    pointOwner : String
    pointEndomorphismTheorem : String
    orderThreeTheorem : String
    localEulerOwner : String
    inertTraceTheorem : String
    localFactorTheorem : String
    verificationStatus : String
    origin : Attribution.ClaimOrigin

open LeanJZeroCMFormalSourceReceipt public

leanJZeroCMReceipt : LeanJZeroCMFormalSourceReceipt
leanJZeroCMReceipt =
  lean-jzero-cm-formal-source-receipt
    "chboishabba/dashi_lean4"
    "PR #73"
    "agent/eisenstein-cm-point-endomorphism-maxcut-20261016"
    "87819b7a86e10eda590996cde0ba2c0f09dbfa41"
    "Integration/EisensteinJZeroPointCMExact.lean"
    "omegaPoint_add / omegaPointEndomorphism"
    "omegaPointEndomorphism_order_three"
    "Integration/EisensteinJZeroLocalEulerExact.lean"
    "inertFiveTraceZero"
    "inertFiveLocalFactor"
    "SOURCE-WRITTEN / PINNED-MATHLIB-API-AUDITED / KERNEL-PENDING"
    Attribution.leanFormalReconstruction

leanJZeroCMClaimOrigin : Attribution.ClaimOrigin
leanJZeroCMClaimOrigin = origin leanJZeroCMReceipt

------------------------------------------------------------------------
-- Exact receipt status.
------------------------------------------------------------------------

leanActualEllipticPointCarrierObserved : Bool
leanActualEllipticPointCarrierObserved = true

leanSameCurveGroupEndomorphismSourceObserved : Bool
leanSameCurveGroupEndomorphismSourceObserved = true

leanOrderThreeEndomorphismSourceObserved : Bool
leanOrderThreeEndomorphismSourceObserved = true

leanLiteralInertFiveEulerRowObserved : Bool
leanLiteralInertFiveEulerRowObserved = true

leanProofObjectImportedIntoAgda : Bool
leanProofObjectImportedIntoAgda = false

leanKernelVerificationObserved : Bool
leanKernelVerificationObserved = false

agdaSameCurveGroupEndomorphismInhabitedFromReceipt : Bool
agdaSameCurveGroupEndomorphismInhabitedFromReceipt = false

fullCMEndomorphismRingIdentified : Bool
fullCMEndomorphismRingIdentified = false

heckeCharacterConstructed : Bool
heckeCharacterConstructed = false

allLocalEulerFactorsIdentified : Bool
allLocalEulerFactorsIdentified = false

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record EisensteinJZeroCMCrossProverBoundary : Set where
  constructor eisenstein-jzero-cm-cross-prover-boundary
  field
    leanPointEndomorphismSourceRecorded : Bool
    leanLocalEulerSourceRecorded : Bool
    agdaKernelAuthorityImported : Bool
    agdaPointEndomorphismManufactured : Bool
    fullCMRingManufactured : Bool
    heckeCharacterManufactured : Bool
    allEulerFactorsManufactured : Bool

canonicalBoundary : EisensteinJZeroCMCrossProverBoundary
canonicalBoundary =
  eisenstein-jzero-cm-cross-prover-boundary
    true
    true
    false
    false
    false
    false
    false
