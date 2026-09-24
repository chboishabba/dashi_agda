module DASHI.Analysis.RiemannG2GammaPoleCancellationRatioTransferLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GAMMA-TO-POLE RATIO SEPARATION -> CENTERED GAMMA SIGN
--
-- Companion Lean source now owns the scalar transfer theorem behind the
-- canonical two-window argument.
--
-- If
--
--   P_in < 0 < P_out,
--   P_in + lambda P_out = 0,
--   G_in  = R_in  P_in,
--   G_out = R_out P_out,
--   R_in < R_out,
--
-- then
--
--   0 < G_in + lambda G_out
--
-- and therefore for the literal Gamma cone convention
--
--   Q_Gamma = -2 (G_in + lambda G_out)
--
-- one obtains
--
--   Q_Gamma < 0.
--
-- A quantitative version is also source-written: if
--
--   d <= R_out - R_in,
--
-- then
--
--   Q_Gamma <= -2 (-P_in) d.
--
-- The remaining analytic payment is NOT this algebra.  It is the actual
-- identical-affine-bump integral instantiation which extracts a concrete
-- positive ratio gap d from the source-written pointwise ratio monotonicity.
------------------------------------------------------------------------

record GammaPoleCancellationRatioTransferReceipt : Set where
  constructor gamma-pole-cancellation-ratio-transfer-receipt
  field
    repository : String
    branch : String
    sourcePath : String
    qualitativeTheorem : String
    quantitativeTheorem : String
    sourceCommit : String

open GammaPoleCancellationRatioTransferReceipt public

currentGammaPoleCancellationRatioTransferReceipt :
  GammaPoleCancellationRatioTransferReceipt
currentGammaPoleCancellationRatioTransferReceipt =
  gamma-pole-cancellation-ratio-transfer-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannGammaPoleCancellationRatioTransfer.lean"
    "Synthesis.poleCancellation_ratioSeparation_gammaCone_neg"
    "Synthesis.poleCancellation_ratioGap_gammaCone_upper"
    "3e946e69dc9d9a7353490b11f2793b968d8ddca3"

record GammaPoleCancellationRatioTransferBoundary : Set where
  constructor gamma-pole-cancellation-ratio-transfer-boundary
  field
    poleCancellationToGammaSignAlgebraSourceWritten : Bool
    quantitativeRatioGapToGammaDeficitSourceWritten : Bool
    projectiveBalanceImported : Bool
    finalBalanceImported : Bool

    identicalAffineBumpIntegralInstantiationPaid : Bool
    concreteRatioGapPaid : Bool
    gammaDominatesCanonicalFarPaid : Bool
    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgda : Bool
    r2ClosedHere : Bool
    rhDerivedHere : Bool

open GammaPoleCancellationRatioTransferBoundary public

canonicalGammaPoleCancellationRatioTransferBoundary :
  GammaPoleCancellationRatioTransferBoundary
canonicalGammaPoleCancellationRatioTransferBoundary =
  gamma-pole-cancellation-ratio-transfer-boundary
    true
    true
    false
    false

    false
    false
    false
    false
    false
    false
    false

ratioTransferAlgebraNoLongerFreshMath :
  GammaPoleCancellationRatioTransferBoundary.poleCancellationToGammaSignAlgebraSourceWritten
    canonicalGammaPoleCancellationRatioTransferBoundary ≡ true
ratioTransferAlgebraNoLongerFreshMath = refl

concreteIntegratedRatioGapStillOpen :
  GammaPoleCancellationRatioTransferBoundary.concreteRatioGapPaid
    canonicalGammaPoleCancellationRatioTransferBoundary ≡ false
concreteIntegratedRatioGapStillOpen = refl
