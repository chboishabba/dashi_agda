module DASHI.Analysis.RiemannG2QuantitativeCanonicalGammaConeDeficitLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LITERAL QUANTITATIVE CANONICAL GAMMA CONE DEFICIT
--
-- Companion Lean now closes the remaining Gamma-side instantiation debt on the
-- actual canonical pole-killing taper.
--
-- For t >= 18 it proves, on the literal final Gamma cone:
--
--   Q_Gamma
--     <= -2 * ((-P_inner) * canonicalGammaRatioGap(t))
--
-- and therefore
--
--   Q_Gamma < 0.
--
-- This theorem uses:
--
--   * the actual quantitative inner/outer bumps,
--   * the actual pole-cancelling lambda,
--   * the exact time-domain Gamma kernel bridge,
--   * endpoint ratio monotonicity,
--   * integrated inner/outer Gamma lower bounds,
--   * and the literal gammaConeValue_exact consumer.
--
-- Consequently the H2e frontier is no longer a Gamma same-object problem.
-- The remaining high analytic payment is entirely on the Off side:
--
--   normalized zero-weighted shell aggregate
--      < 2 * (-P_inner) * canonicalGammaRatioGap(t).
------------------------------------------------------------------------

record QuantitativeCanonicalGammaConeDeficitReceipt : Set where
  constructor quantitative-canonical-gamma-cone-deficit-receipt
  field
    repository : String
    branch : String
    kernelBridgePath : String
    deficitPath : String
    rootWiringCommit : String

open QuantitativeCanonicalGammaConeDeficitReceipt public

currentQuantitativeCanonicalGammaConeDeficitReceipt :
  QuantitativeCanonicalGammaConeDeficitReceipt
currentQuantitativeCanonicalGammaConeDeficitReceipt =
  quantitative-canonical-gamma-cone-deficit-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannGammaCenteredKernelCompactBridge.lean"
    "Synthesis/RiemannQuantitativeGammaDeficit.lean"
    "2d34675cea00a50e7f11bafa6438905559bd68a5"

record QuantitativeCanonicalGammaConeDeficitBoundary : Set where
  constructor quantitative-canonical-gamma-cone-deficit-boundary
  field
    literalCanonicalInnerGammaInstantiationSourceWritten : Bool
    literalCanonicalOuterGammaInstantiationSourceWritten : Bool
    literalCanonicalGammaConeDeficitSourceWritten : Bool
    literalCanonicalGammaConeStrictNegativeSourceWritten : Bool

    gammaSameObjectInstantiationStillOpenForH2e : Bool
    normalizedOffAggregateBelowGammaDeficitStillRequired : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgdaKernelHere : Bool
    h2eClosedHere : Bool
    r2ClosedHere : Bool
    rhDerivedHere : Bool

open QuantitativeCanonicalGammaConeDeficitBoundary public

canonicalQuantitativeCanonicalGammaConeDeficitBoundary :
  QuantitativeCanonicalGammaConeDeficitBoundary
canonicalQuantitativeCanonicalGammaConeDeficitBoundary =
  quantitative-canonical-gamma-cone-deficit-boundary
    true
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

gammaLiteralInstantiationNoLongerOpen :
  QuantitativeCanonicalGammaConeDeficitBoundary.gammaSameObjectInstantiationStillOpenForH2e
    canonicalQuantitativeCanonicalGammaConeDeficitBoundary ≡ false
gammaLiteralInstantiationNoLongerOpen = refl

offAggregateIsTheRemainingH2ePayment :
  QuantitativeCanonicalGammaConeDeficitBoundary.normalizedOffAggregateBelowGammaDeficitStillRequired
    canonicalQuantitativeCanonicalGammaConeDeficitBoundary ≡ true
offAggregateIsTheRemainingH2ePayment = refl
