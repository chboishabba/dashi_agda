module DASHI.Analysis.RiemannG2CenteredComplementSignBoundaryLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CENTERED COMPLEMENT SIGN BOUNDARY
--
-- Exact centering gives
--
--   h_r(u) = g(u)(cos(r u)-1) <= 0
--
-- for the canonical nonnegative taper.
--
-- But a final off-ordinate reflection-pair kernel is
--
--   4 h_r(u) cosh(a u) cos(delta u),
--
-- and the oscillatory cosine can reverse the sign.
--
-- Companion Lean source gives a concrete witness: at a gap with cosine -1,
-- a strictly negative taper value produces a strictly positive pair kernel.
--
-- Therefore:
--
--   h_r <= 0
--
-- does NOT imply the desired centered final-complement sign by a pointwise
-- positivity argument.  Any proof of that sign must use global oscillatory
-- cancellation / summed response structure (and the Gamma channel as well).
------------------------------------------------------------------------

record CenteredComplementSignBoundaryLeanReceipt : Set where
  constructor centered-complement-sign-boundary-lean-receipt
  field
    repository : String
    branch : String
    sourcePath : String
    sourceCommit : String

open CenteredComplementSignBoundaryLeanReceipt public

currentCenteredComplementSignBoundaryLeanReceipt :
  CenteredComplementSignBoundaryLeanReceipt
currentCenteredComplementSignBoundaryLeanReceipt =
  centered-complement-sign-boundary-lean-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannCenteredComplementSignBoundary.lean"
    "6696cd9247fc479e7ea53662f0e34deff1b6aff9"

record CenteredComplementSignBoundary : Set where
  constructor centered-complement-sign-boundary
  field
    centeredTaperNonpositiveSourceWritten : Bool
    pointwiseOffPairSignFollowsFromTaperSign : Bool
    pointwiseSignReversalWitnessSourceWritten : Bool

    centeredComplementSignStillGlobalAnalyticTheorem : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgda : Bool
    r2ClosedHere : Bool
    rhDerivedHere : Bool

open CenteredComplementSignBoundary public

canonicalCenteredComplementSignBoundary :
  CenteredComplementSignBoundary
canonicalCenteredComplementSignBoundary =
  centered-complement-sign-boundary
    true
    false
    true

    true

    false
    false
    false
    false
