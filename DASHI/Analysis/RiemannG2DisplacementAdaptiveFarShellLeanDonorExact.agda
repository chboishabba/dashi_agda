module DASHI.Analysis.RiemannG2DisplacementAdaptiveFarShellLeanDonorExact where

------------------------------------------------------------------------
-- ADAPTIVE FAR-SHELL DONOR
--
-- Fixed J=t^4 gives 144*A/t^2, but the cluster surplus vanishes like a^2.
-- For uniform arbitrary off-line zeros that fixed schedule cannot by itself fit
-- the cluster window as a -> 0.
--
-- Companion Lean source now proves the domain-neutral adaptive atom
--
--   J_real = (t/alpha)^4
--
-- gives
--
--   farShell(A,t,J_real) <= 144*A*alpha^2/t^2
--
-- for t>=1 and 0<alpha<=1.
--
-- The remaining literal-carrier work is to choose an admissible NATURAL cutoff
-- at least this large, preserve the near/crossing requirements, and transport
-- the resulting far-shell theorem onto the final Off carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record DisplacementAdaptiveFarShellReceipt : Set where
  constructor displacement-adaptive-far-shell-receipt
  field
    repository : String
    branch : String
    sourcePath : String
    regressionPath : String
    theoremName : String
    sourceCommit : String
    regressionCommit : String

open DisplacementAdaptiveFarShellReceipt public

currentDisplacementAdaptiveFarShellReceipt : DisplacementAdaptiveFarShellReceipt
currentDisplacementAdaptiveFarShellReceipt =
  displacement-adaptive-far-shell-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannFarShellDisplacementAdaptiveCutoff.lean"
    "Synthesis/RiemannFarShellDisplacementAdaptiveCutoffRegression.lean"
    "Synthesis.farShell_scaledQuartic_le_displacementInverseSquare"
    "412450e3686de10b804581da1af8760225bf5a28"
    "e0f92cb01c3919f4681f27e4955e3f73c1097972"

record DisplacementAdaptiveFarShellBoundary : Set where
  constructor displacement-adaptive-far-shell-boundary
  field
    fixedQuarticRateSourceWritten : Bool
    fixedQuarticRateUniformlySufficientAsHorizontalDisplacementTendsToZero : Bool
    adaptiveRealCutoffRateSourceWritten : Bool
    adaptiveRateMatchesHorizontalSquareScale : Bool
    naturalCutoffAttachmentPaid : Bool
    crossingAdmissionForAdaptiveCutoffPaid : Bool
    finalFarCarrierTransportPaid : Bool
    rhDerivedHere : Bool

open DisplacementAdaptiveFarShellBoundary public

canonicalDisplacementAdaptiveFarShellBoundary :
  DisplacementAdaptiveFarShellBoundary
canonicalDisplacementAdaptiveFarShellBoundary =
  displacement-adaptive-far-shell-boundary
    true
    false
    true
    true
    false
    false
    false
    false
