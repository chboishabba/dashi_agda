module DASHI.Foundations.BishopPointwiseApproximationOrderExact where

------------------------------------------------------------------------
-- POINTWISE ORDER OF REGULAR RATIONAL APPROXIMANTS -> BISHOP-REAL ORDER
--
-- The vendored Bishop real order is defined by
--
--   x <= y  :=  NonNegative (y - x),
--
-- and NonNegative only requires the sampled difference at precision n to be
-- at least -1/n.  For reals built from regular rational approximants, a
-- pointwise rational order is stronger: the sampled difference is >= 0.
--
-- This owner packages that generic transport once so domain modules do not
-- need to re-prove the vendor representation boundary.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base as NatBase using (NonZero)
open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; 0ℚᵘ; _/_; _-_; _≤_)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as BishopReal
import DASHI.Foundations.BishopRegularRationalApproximationExact as Approx
import DASHI.Foundations.BishopSquareNonnegativeExact as Square

pointwiseApproximationOrderRealizesBishopOrder :
  (left right : Approx.BishopRegularRationalApproximation) →
  ((precision : Nat) → .{{_ : NonZero precision}} →
    Approx.approximation left precision
      ℚ.≤ Approx.approximation right precision) →
  BishopReal._≤_
    (Approx.realizeRegularApproximation left)
    (Approx.realizeRegularApproximation right)
pointwiseApproximationOrderRealizesBishopOrder left right ordered =
  BishopReal.nonNeg* λ precision {precision≢0} →
    let
      instance
        precisionNonZero : NonZero precision
        precisionNonZero = NatBase.≢-nonZero precision≢0

      doubledPrecision = 2 * precision

      pointwise :
        Approx.approximation left doubledPrecision
        ℚ.≤ Approx.approximation right doubledPrecision
      pointwise = ordered doubledPrecision

      differenceNonnegative :
        0ℚᵘ ℚ.≤
        (Approx.approximation right doubledPrecision
          ℚ.- Approx.approximation left doubledPrecision)
      differenceNonnegative = ℚP.p≤q⇒0≤q-p pointwise

      toleranceBelowZero :
        ℚ.- (+ 1 / precision) ℚ.≤ 0ℚᵘ
      toleranceBelowZero = Square.negativeOneOverBelowZero precision
    in
    ℚP.≤-trans toleranceBelowZero differenceNonnegative

bishopPointwiseApproximationOrderTransportClosed : Agda.Builtin.Bool.Bool
bishopPointwiseApproximationOrderTransportClosed = Agda.Builtin.Bool.true
