module DASHI.Analysis.RiemannG2CenteredNearCoreSignLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CENTERED FINITE-NEAR SIGN ON THE FINAL UNIVERSAL CARRIER
--
-- Companion Lean source proves for h_r = g(cos(ru)-1) and nonnegative g:
--
--   |delta| Lambda <= pi/2
--     -> each reflection-pair response for h_r is <= 0.
--
-- Therefore, for the exact final finite near finset,
--
--   J Lambda <= pi/2
--     -> sum_{sigma in near(J)} finalPairTerm(h_r,sigma) <= 0.
--
-- Combining this with the final near/far decomposition yields:
--
--   centered Off <= explicit far remainder.
--
-- This removes the finite signed near core as a positive analytic risk inside
-- the cosine window.  It does not prove the whole centered complement sign.
------------------------------------------------------------------------

record CenteredNearCoreSignLeanReceipt : Set where
  constructor centered-near-core-sign-lean-receipt
  field
    repository : String
    branch : String
    nearSignPath : String
    farOnlyPath : String
    nearSignCommit : String
    farOnlyCommit : String

open CenteredNearCoreSignLeanReceipt public

currentCenteredNearCoreSignLeanReceipt : CenteredNearCoreSignLeanReceipt
currentCenteredNearCoreSignLeanReceipt =
  centered-near-core-sign-lean-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannCenteredNearPairSign.lean"
    "Synthesis/RiemannCenteredOffFarOnlyUpper.lean"
    "dde525728d92b595489d7675a6635f11d1a49c57"
    "83cace2cca2de03361560bc5de5140257293b584"

record CenteredNearCoreSignBoundary : Set where
  constructor centered-near-core-sign-boundary
  field
    pairSignInsideCosineWindowSourceWritten : Bool
    finalFiniteNearCoreNonpositiveSourceWritten : Bool
    centeredOffReducedToFarRemainderSourceWritten : Bool

    independentNearCancellationEstimateStillRequiredInsideWindow : Bool
    wholeCenteredComplementSignPaid : Bool
    gammaCenteredSignPaid : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgda : Bool
    r2ClosedHere : Bool
    rhDerivedHere : Bool

open CenteredNearCoreSignBoundary public

canonicalCenteredNearCoreSignBoundary : CenteredNearCoreSignBoundary
canonicalCenteredNearCoreSignBoundary =
  centered-near-core-sign-boundary
    true
    true
    true

    false
    false
    false

    false
    false
    false
    false
