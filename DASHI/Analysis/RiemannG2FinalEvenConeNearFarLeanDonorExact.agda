module DASHI.Analysis.RiemannG2FinalEvenConeNearFarLeanDonorExact where

------------------------------------------------------------------------
-- FINAL UNIVERSAL EVEN-CONE SIGNED NEAR/FAR DONOR
--
-- Companion Lean source now proves the cutoff decomposition directly on the
-- actual universal even-cone off-ordinate response:
--
--   D_off(g,t,s)
--     = 1/2 * finiteSignedNear(g,t,s,J) + R_J
--
-- with
--
--   |R_J| <= 1/2 * C_s * farShellBound A |t| J
--
-- and R_J -> 0 as J -> infinity.
--
-- The construction absorbs the literal sample cosine into
--
--   g_s(u) = g(u) cos(su)
--
-- and reuses the existing reflection-pair O(delta^-2) theorem on that sampled
-- taper.  No determinant/projective response or projective-balance transport is
-- used.
--
-- This is a theorem-source donor, not an Agda proof transport and not yet the
-- R1 equality nearResponseAt(J)=finiteNearSum(cellResponse).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record FinalEvenConeNearFarLeanReceipt : Set where
  constructor final-even-cone-near-far-lean-receipt
  field
    repository : String
    branch : String
    sourcePath : String
    regressionPath : String
    theoremName : String
    sourceCommit : String
    regressionCommit : String

open FinalEvenConeNearFarLeanReceipt public

currentFinalEvenConeNearFarLeanReceipt : FinalEvenConeNearFarLeanReceipt
currentFinalEvenConeNearFarLeanReceipt =
  final-even-cone-near-far-lean-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannFinalEvenConeNearFarSplit.lean"
    "Synthesis/RiemannFinalEvenConeNearFarSplitRegression.lean"
    "Synthesis.exists_finalEvenCone_near_far_split"
    "6a4f2cea290598abaa79082311b43e2151aab738"
    "7875b10e39b755319f37968d6d78fec734ca73f3"

record FinalEvenConeNearFarDonorBoundary : Set where
  constructor final-even-cone-near-far-donor-boundary
  field
    theoremSourceWritten : Bool
    finalUniversalEvenConeConsumerUsed : Bool
    projectiveCarrierBridgeRequired : Bool
    finiteNearCoreRemainsSigned : Bool
    explicitFarRemainderOwnedAtSource : Bool
    farRemainderTendsToZeroOwnedAtSource : Bool

    adaptiveNearProblemReducedToFiniteSignedCoreControl : Bool

    exactR1NearObserverEqualityPaid : Bool
    chosenAdaptiveCutoffAttachedToFinalAgdaCarrier : Bool
    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgda : Bool
    r2ClosedHere : Bool
    rhDerivedHere : Bool

open FinalEvenConeNearFarDonorBoundary public

canonicalFinalEvenConeNearFarDonorBoundary :
  FinalEvenConeNearFarDonorBoundary
canonicalFinalEvenConeNearFarDonorBoundary =
  final-even-cone-near-far-donor-boundary
    true
    true
    false
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
