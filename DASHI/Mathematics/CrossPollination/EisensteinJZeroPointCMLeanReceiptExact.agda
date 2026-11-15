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
    inertEulerOwner : String
    inertFamilyTheorem : String
    primaryOwner : String
    primaryTheorem : String
    characterSumOwner : String
    characterSumTheorem : String
    remainingFrontier : String
    verificationStatus : String
    origin : Attribution.ClaimOrigin

open LeanJZeroCMFormalSourceReceipt public

leanJZeroCMReceipt : LeanJZeroCMFormalSourceReceipt
leanJZeroCMReceipt =
  lean-jzero-cm-formal-source-receipt
    "chboishabba/dashi_lean4"
    "PR #73"
    "agent/eisenstein-cm-point-endomorphism-maxcut-20261016"
    "4dde2b77cbdb76bdb21db852966db2ffa0ca88d3"
    "Integration/EisensteinJZeroPointCMExact.lean"
    "omegaPoint_add / omegaPointEndomorphism / omegaPointEndomorphism_order_three"
    "Integration/EisensteinJZeroInertPrimeEulerExact.lean"
    "localEulerPolynomial_inert"
    "Integration/EisensteinJZeroPrimaryNormalizationExact.lean"
    "splitPrime_primary_associate_existsUnique"
    "Integration/EisensteinJZeroQuadraticCharacterTraceExact.lean"
    "frobeniusTrace_eq_neg_characterSum"
    "cubic/Jacobi-sum evaluation -> primary trace -> CM Hecke character -> global elliptic/Hecke L-series"
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

leanAllInertPrimeLocalEulerSourceObserved : Bool
leanAllInertPrimeLocalEulerSourceObserved = true

leanSplitPrimePrimaryNormalizationObserved : Bool
leanSplitPrimePrimaryNormalizationObserved = true

leanFrobeniusQuadraticCharacterSumObserved : Bool
leanFrobeniusQuadraticCharacterSumObserved = true

leanCubicJacobiEvaluationObserved : Bool
leanCubicJacobiEvaluationObserved = false

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
    leanPrimaryNormalizationSourceRecorded : Bool
    leanQuadraticCharacterTraceSourceRecorded : Bool
    leanCubicJacobiEvaluationRecorded : Bool
    agdaKernelAuthorityImported : Bool
    fullCMRingManufactured : Bool
    heckeCharacterManufactured : Bool
    allSplitEulerFactorsManufactured : Bool

canonicalBoundary : EisensteinJZeroCMCrossProverBoundary
canonicalBoundary =
  eisenstein-jzero-cm-cross-prover-boundary
    true
    true
    true
    true
    false
    false
    false
    false
    false
