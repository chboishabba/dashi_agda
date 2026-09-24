module DASHI.Analysis.RiemannG2NormalizedHorizontalCorrectionLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NORMALIZED HORIZONTAL-STRIP CORRECTION BOUND
--
-- Companion Lean splits the normalized atom as
--
--   Phi_t(q)
--     + E_t(alpha,q),
--
-- where alpha = heightOf(rho)/t.
--
-- It now proves:
--
--   H_t(v) != 0 -> |v| < 9*pi/4,
--
--   |x| <= 1 -> 0 <= cosh(x)-1 <= x^2,
--
-- and, using |heightOf rho| <= 1/2 and t >= 18,
--
--   |E_t(heightOf(rho)/t,q_rho)|
--      <= M2(t) / t^2,
--
-- with
--
--   M2(t) = integral |H_t(v)| v^2 dv.
--
-- Consequently, for every finite literal zero carrier F,
--
--   |horizontalAggregate_t(F)|
--      <= (M2(t)/t^2) * totalMultiplicity(F).
--
-- The literal centered-Off aggregate itself has the additional 1/t Jacobian,
-- so this term enters at t^{-3} times finite multiplicity.
--
-- Therefore horizontal strip variation is no longer the analytic min-cut.
-- The remaining collective high-side theorem is the one-dimensional normalized
-- q-counting/Riemann--von Mangoldt remainder pairing.
------------------------------------------------------------------------

record NormalizedHorizontalCorrectionReceipt : Set where
  constructor normalized-horizontal-correction-receipt
  field
    repository : String
    branch : String
    path : String
    commit : String
    rootWiringCommit : String

open NormalizedHorizontalCorrectionReceipt public

currentNormalizedHorizontalCorrectionReceipt :
  NormalizedHorizontalCorrectionReceipt
currentNormalizedHorizontalCorrectionReceipt =
  normalized-horizontal-correction-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannNormalizedHorizontalCorrectionBound.lean"
    "1a8a7596b601937692383051f3ed8ed892daf4ca"
    "ad68ae096fbdefa435c13a0f6177736fd76e5041"

record NormalizedHorizontalCorrectionBoundary : Set where
  constructor normalized-horizontal-correction-boundary
  field
    fixedNormalizedSupportUpperSourceWritten : Bool
    coshQuadraticSmallArgumentBoundSourceWritten : Bool
    actualZeroHorizontalArgumentSmallSourceWritten : Bool
    perZeroHorizontalCorrectionTMinusTwoSourceWritten : Bool
    finiteHorizontalAggregateBoundSourceWritten : Bool

    rvMCountingRemainderPairBoundPaid : Bool
    aggregateOffBelowGammaDeficitPaid : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgdaKernelHere : Bool
    h2AggregateClosedHere : Bool
    r2ClosedHere : Bool
    rhDerivedHere : Bool

open NormalizedHorizontalCorrectionBoundary public

canonicalNormalizedHorizontalCorrectionBoundary :
  NormalizedHorizontalCorrectionBoundary
canonicalNormalizedHorizontalCorrectionBoundary =
  normalized-horizontal-correction-boundary
    true
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
    false

horizontalCorrectionBoundNowSourceWritten :
  NormalizedHorizontalCorrectionBoundary.finiteHorizontalAggregateBoundSourceWritten
    canonicalNormalizedHorizontalCorrectionBoundary ≡ true
horizontalCorrectionBoundNowSourceWritten = refl

rvMCountingRemainderIsSoleCollectiveHighDebt :
  NormalizedHorizontalCorrectionBoundary.rvMCountingRemainderPairBoundPaid
    canonicalNormalizedHorizontalCorrectionBoundary ≡ false
rvMCountingRemainderIsSoleCollectiveHighDebt = refl

rhStillFailClosed :
  NormalizedHorizontalCorrectionBoundary.rhDerivedHere
    canonicalNormalizedHorizontalCorrectionBoundary ≡ false
rhStillFailClosed = refl
