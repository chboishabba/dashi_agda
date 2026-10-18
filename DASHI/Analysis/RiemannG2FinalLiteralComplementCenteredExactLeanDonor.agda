module DASHI.Analysis.RiemannG2FinalLiteralComplementCenteredExactLeanDonor where

------------------------------------------------------------------------
-- EXACT CENTERING OF THE FINAL LITERAL COMPLEMENT
--
-- Companion Lean source proves on the actual universal even-cone consumer:
--
--   S_g(t,r) - S_g(t,0) = S_{h_r}(t,0)
--
-- where
--
--   S_g(t,r) = Off_g(t,r) + Q_Gamma,g(t,r)
--   h_r(u)   = g(u) (cos(r u) - 1).
--
-- For nonnegative g, h_r <= 0 pointwise.
--
-- The existing quadratic envelope is therefore only a magnitude theorem around
-- an exact centered identity.  The prize-facing analytic leaf is the sign (or
-- stronger exact cancellation) of S_{h_r}(t,0), not merely another absolute
-- constant improvement.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record FinalLiteralComplementCenteredExactLeanReceipt : Set where
  constructor final-literal-complement-centered-exact-lean-receipt
  field
    repository : String
    branch : String
    sourcePath : String
    sourceCommit : String

open FinalLiteralComplementCenteredExactLeanReceipt public

currentFinalLiteralComplementCenteredExactLeanReceipt :
  FinalLiteralComplementCenteredExactLeanReceipt
currentFinalLiteralComplementCenteredExactLeanReceipt =
  final-literal-complement-centered-exact-lean-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannFinalLiteralComplementCenteredExact.lean"
    "daf8eaa05489a6fa768f637b733da3d3e04af7bc"

record FinalLiteralComplementCenteredExactBoundary : Set where
  constructor final-literal-complement-centered-exact-boundary
  field
    exactCenteredIdentitySourceWritten : Bool
    centeredTaperPointwiseNonpositiveSourceWritten : Bool
    centeredSignImpliesRadiusMonotonicitySourceWritten : Bool

    positiveEnvelopeAloneIsPrizeFacingClosure : Bool
    centeredSignOrExactCancellationStillRequired : Bool

    projectiveCarrierRequired : Bool
    finiteNearCarrierRequiredToStateWholeResponseIdentity : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgda : Bool
    r2ClosedHere : Bool
    rhDerivedHere : Bool

open FinalLiteralComplementCenteredExactBoundary public

canonicalFinalLiteralComplementCenteredExactBoundary :
  FinalLiteralComplementCenteredExactBoundary
canonicalFinalLiteralComplementCenteredExactBoundary =
  final-literal-complement-centered-exact-boundary
    true
    true
    true

    false
    true

    false
    false

    false
    false
    false
    false
