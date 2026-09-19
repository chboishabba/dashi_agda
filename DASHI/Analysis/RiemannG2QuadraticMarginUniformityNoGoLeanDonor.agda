module DASHI.Analysis.RiemannG2QuadraticMarginUniformityNoGoLeanDonor where

------------------------------------------------------------------------
-- UNIFORM QUADRATIC-MARGIN NO-GO
--
-- Companion Lean source proves:
--
--   E > 0, c >= 0
--     -> exists a != 0, c*a^2 < E.
--
-- Therefore no fixed positive error E independent of horizontal displacement a
-- can satisfy
--
--   E < c*a^2
--
-- for every nonzero a arbitrarily close to the critical line.
--
-- Consequence for the current R2 route:
--
--   a positive a-independent centered envelope cannot itself close the literal
--   Clay-uniform strict margin.  The surviving correction must instead have a
--   favourable sign, vanish exactly, or inherit its own a^2 factor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record QuadraticMarginUniformityNoGoLeanReceipt : Set where
  constructor quadratic-margin-uniformity-no-go-lean-receipt
  field
    repository : String
    branch : String
    sourcePath : String
    sourceCommit : String

open QuadraticMarginUniformityNoGoLeanReceipt public

currentQuadraticMarginUniformityNoGoLeanReceipt :
  QuadraticMarginUniformityNoGoLeanReceipt
currentQuadraticMarginUniformityNoGoLeanReceipt =
  quadratic-margin-uniformity-no-go-lean-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannQuadraticMarginUniformityNoGo.lean"
    "adca289e449c0ce2d9731105aa98e7811c3f479b"

record QuadraticMarginUniformityNoGoBoundary : Set where
  constructor quadratic-margin-uniformity-no-go-boundary
  field
    fixedPositiveErrorCannotFitUniformQuadraticMarginSourceWritten : Bool
    positiveAIndependentEnvelopeCanCloseUniformR2 : Bool

    favourableSignCouldBypassNoGo : Bool
    exactCancellationCouldBypassNoGo : Bool
    ownASquaredFactorCouldBypassNoGo : Bool

    leanKernelReceiptOwnedHere : Bool
    transportedIntoAgda : Bool
    rhDerivedHere : Bool

open QuadraticMarginUniformityNoGoBoundary public

canonicalQuadraticMarginUniformityNoGoBoundary :
  QuadraticMarginUniformityNoGoBoundary
canonicalQuadraticMarginUniformityNoGoBoundary =
  quadratic-margin-uniformity-no-go-boundary
    true
    false

    true
    true
    true

    false
    false
    false
