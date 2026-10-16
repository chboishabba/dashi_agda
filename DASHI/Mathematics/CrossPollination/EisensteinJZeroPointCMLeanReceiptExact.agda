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
    inertEulerOwner : String
    inertFamilyTheorem : String
    splitBoundaryOwner : String
    splitBoundaryTheorem : String
    verificationStatus : String
    origin : Attribution.ClaimOrigin

open LeanJZeroCMFormalSourceReceipt public

leanJZeroCMReceipt : LeanJZeroCMFormalSourceReceipt
leanJZeroCMReceipt =
  lean-jzero-cm-formal-source-receipt
    "chboishabba/dashi_lean4"
    "PR #73"
    "agent/eisenstein-cm-point-endomorphism-maxcut-20261016"
    "039bced5d4773b8b360aebfc9619cfc529277586"
    "Integration/EisensteinJZeroPointCMExact.lean"
    "omegaPoint_add / omegaPointEndomorphism"
    "omegaPointEndomorphism_order_three"
    "Integration/EisensteinJZeroInertPrimeEulerExact.lean"
    "localEulerPolynomial_inert"
    "Integration/EisensteinJZeroSplitSevenExact.lean"
    "normSevenDoesNotDetermineTrace / normalizedSevenMatchesFrobeniusTrace"
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

leanAllInertPrimeTraceZeroSourceObserved : Bool
leanAllInertPrimeTraceZeroSourceObserved = true

leanAllInertPrimeLocalEulerSourceObserved : Bool
leanAllInertPrimeLocalEulerSourceObserved = true

leanSplitSevenNormalizationBoundaryObserved : Bool
leanSplitSevenNormalizationBoundaryObserved = true

leanNormAloneInsufficientForSplitTraceObserved : Bool
leanNormAloneInsufficientForSplitTraceObserved = true

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

allSplitPrimeEulerFactorsIdentified : Bool
allSplitPrimeEulerFactorsIdentified = false

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record EisensteinJZeroCMCrossProverBoundary : Set where
  constructor eisenstein-jzero-cm-cross-prover-boundary
  field
    leanPointEndomorphismSourceRecorded : Bool
    leanAllInertEulerSourceRecorded : Bool
    leanSplitNormalizationBoundaryRecorded : Bool
    agdaKernelAuthorityImported : Bool
    agdaPointEndomorphismManufactured : Bool
    fullCMRingManufactured : Bool
    heckeCharacterManufactured : Bool
    allSplitEulerFactorsManufactured : Bool

canonicalBoundary : EisensteinJZeroCMCrossProverBoundary
canonicalBoundary =
  eisenstein-jzero-cm-cross-prover-boundary
    true
    true
    true
    false
    false
    false
    false
    false
