module DASHI.Analysis.BishopComplexTriangleTailsVanishingExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP FINITE POSITIVE CAUCHY TRIANGLE COMPARISON.
--
-- Comparison is proved via the existing Bishop Sequence.∑₀-mono-≤
-- and the already-proved FinSum.finSumIsSeriesOf bridge.
-- The complete original positive exponential triangle-tail convergence
-- is reused from BishopExponentialCauchyProductExact.
--
-- Unpaid: componentwise factorial-complex term majorization on all
-- indices, followed by domination of differences of positive prefixes.
-- No claim of a completed four-wing vanishing theorem is made here.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Fin.Base using (toℕ)
import Data.Nat.Base as ℕ

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopExponentialCauchyProductExact as ExpCauchy

originalBishopFiniteFinSumMonotone :
  ∀ {left right : Nat → BishopReal.ℝ} →
  (∀ index → BishopReal._≤_ (left index) (right index)) →
  ∀ count →
  BishopReal._≤_
    (FinSum.finSum left count)
    (FinSum.finSum right count)
originalBishopFiniteFinSumMonotone
  {left} {right} pointwise count =
  BishopP.≤-respʳ-≃
    (BishopP.≃-symm
      (FinSum.finSumIsSeriesOf right count))
    (BishopP.≤-respˡ-≃
      (BishopP.≃-symm
        (FinSum.finSumIsSeriesOf left count))
      (BishopSequence.∑₀-mono-≤ pointwise count))

originalBishopCauchyCoefficientMonotone :
  ∀ {a b A B : Nat → BishopReal.ℝ} →
  (∀ n → BishopReal._≤_ (a n) (A n)) →
  (∀ n → BishopReal._≤_ (b n) (B n)) →
  (∀ n → BishopReal.NonNegative (A n)) →
  (∀ n → BishopReal.NonNegative (b n)) →
  ∀ count →
  BishopReal._≤_
    (Row.cauchyCoefficient a b count)
    (Row.cauchyCoefficient A B count)
originalBishopCauchyCoefficientMonotone
  {a} {b} {A} {B} a≤A b≤B Ann bnn count =
  originalBishopFiniteFinSumMonotone
    (λ index →
      BishopP.≤-trans
        (BishopP.*-monoʳ-≤-nonNeg
          (a≤A index)
          (bnn (count ℕ.∸ index)))
        (BishopP.*-monoˡ-≤-nonNeg
          (b≤B (count ℕ.∸ index))
          (Ann index)))
    (suc count)

originalBishopCauchyTriangleMonotone :
  ∀ {a b A B : Nat → BishopReal.ℝ} →
  (∀ n → BishopReal._≤_ (a n) (A n)) →
  (∀ n → BishopReal._≤_ (b n) (B n)) →
  (∀ n → BishopReal.NonNegative (A n)) →
  (∀ n → BishopReal.NonNegative (b n)) →
  ∀ count →
  BishopReal._≤_
    (Row.trianglePartial a b count)
    (Row.trianglePartial A B count)
originalBishopCauchyTriangleMonotone
  {a} {b} {A} {B} a≤A b≤B Ann bnn count =
  originalBishopFiniteFinSumMonotone
    (originalBishopCauchyCoefficientMonotone
      a≤A b≤B Ann bnn)
    count

-- This convergence is not a newly proposed witness. It is the
-- pinned Bishop real factorial exponential triangle-tail theorem.
originalBishopFactorialPositiveTriangleTailVanishes :
  ∀ x y →
  BishopSequence._ConvergesTo_
    (ExpCauchy.absoluteTriangleWingTail x y)
    BishopReal.0ℝ
originalBishopFactorialPositiveTriangleTailVanishes =
  ExpCauchy.absoluteTriangleWingTailConvergesZero
