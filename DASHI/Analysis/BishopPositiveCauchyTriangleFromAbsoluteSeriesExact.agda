{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopPositiveCauchyTriangleFromAbsoluteSeriesExact where

------------------------------------------------------------------------
-- K05: POSITIVE CAUCHY TRIANGLES FROM TWO ACTUALLY CONVERGENT
-- NONNEGATIVE BISHOP-REAL SERIES.
--
-- Finite geometry already proved in the repository:
--    R(n,n) <= T(2n) <= R(2n,2n)
-- for nonnegative coefficient histories.  Both rectangles converge
-- to the same genuine product via the pinned Sequence multiplication.
-- Native order squeeze proves T(2n) converges to that product.
-- The positive triangle is nondecreasing; the native double-subsequence
-- theorem upgrades T(2n)->L to ALL T(n)->L.
--
-- There are no abstract CauchyProduct/MonotoneConvergence authorities
-- and no arbitrary series limits in the theorem statement.
-- Proof source: Cauchy; Bishop/Bridges; Murray/Csimma, plus the original
-- DASHI finite rectangle/triangle order and real-setoid proofs.
-- Agda kernel acceptance is still required.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc; _+_)
import Data.Nat.Base as N
open import Relation.Binary.PropositionalEquality using (cong; sym)
open import Data.Product.Base using (proj₁; proj₂)

import Real as R
import RealProperties as RP
import Sequence as S

import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopFiniteSeriesRectangleProductExact as Rect
import DASHI.Foundations.BishopFiniteRectangleInsideCauchyTriangleExact as RectInside
import DASHI.Foundations.BishopFiniteCauchyTriangleInsideRectangleExact as TriInside
import DASHI.Foundations.BishopExponentialCauchyProductExact as Exp
import DASHI.Analysis.BishopConvergentDoubleTailExact as Double
import DASHI.Analysis.BishopGenericCauchyFromAbsoluteTriangleExact as Generic
import DASHI.Analysis.BishopSetoidSqueezeConvergenceExact as Squeeze
import DASHI.Analysis.BishopMonotoneDoubleSubsequenceLimitExact as Monotone

positiveCauchyCoefficientNonnegative :
  (left right : Nat → R.ℝ) →
  (leftNonnegative : ∀ n → R.NonNegative (left n)) →
  (rightNonnegative : ∀ n → R.NonNegative (right n)) →
  (degree : Nat) →
  R.NonNegative (Row.cauchyCoefficient left right degree)
positiveCauchyCoefficientNonnegative
    left right leftNonnegative rightNonnegative degree =
  RectInside.finPrefixNonnegative
    (λ k →
      RP.nonNegx,y⇒nonNegx*y
        (leftNonnegative k)
        (rightNonnegative (degree N.∸ k)))
    (suc degree)

positiveCauchyTriangleIncreasing :
  (left right : Nat → R.ℝ) →
  (leftNonnegative : ∀ n → R.NonNegative (left n)) →
  (rightNonnegative : ∀ n → R.NonNegative (right n)) →
  S._isIncreasing (Row.trianglePartial left right)
positiveCauchyTriangleIncreasing
    left right leftNonnegative rightNonnegative count =
  let
    coefficients = Row.cauchyCoefficient left right
    nativeIncreasing =
      RectInside.partialSumsIncreasing
        (positiveCauchyCoefficientNonnegative
          left right leftNonnegative rightNonnegative)
  in
  RP.≤-respʳ-≃
    (RP.≃-symm (FinSum.finSumIsSeriesOf coefficients (suc count)))
    (RP.≤-respˡ-≃
      (RP.≃-symm (FinSum.finSumIsSeriesOf coefficients count))
      (nativeIncreasing count))

nonnegativeRectangleBelowEvenTriangle :
  (left right : Nat → R.ℝ) →
  (leftNonnegative : ∀ n → R.NonNegative (left n)) →
  (rightNonnegative : ∀ n → R.NonNegative (right n)) →
  (count : Nat) →
  R._≤_
    (Rect.rectangleSum left right count count)
    (Row.trianglePartial left right (Double.double count))
nonnegativeRectangleBelowEvenTriangle
    left right leftNN rightNN count =
  RP.≤-respʳ-≃
    (RP.≃-refl₂
      (cong (Row.trianglePartial left right)
        (sym (Exp.doubleIsAddSelf count))))
    (RectInside.rectangleInsideTriangle leftNN rightNN count count)

nonnegativeEvenTriangleBelowDoubleRectangle :
  (left right : Nat → R.ℝ) →
  (leftNonnegative : ∀ n → R.NonNegative (left n)) →
  (rightNonnegative : ∀ n → R.NonNegative (right n)) →
  (count : Nat) →
  R._≤_
    (Row.trianglePartial left right (Double.double count))
    (Rect.rectangleSum left right
      (Double.double count) (Double.double count))
nonnegativeEvenTriangleBelowDoubleRectangle
    left right leftNN rightNN count =
  TriInside.triangleInsideSquare
    leftNN rightNN (Double.double count)

positiveCauchyEvenTriangleConverges :
  (left right : Nat → R.ℝ) →
  (leftNonnegative : ∀ n → R.NonNegative (left n)) →
  (rightNonnegative : ∀ n → R.NonNegative (right n)) →
  (leftConvergence : S._isConvergent (S.SeriesOf left)) →
  (rightConvergence : S._isConvergent (S.SeriesOf right)) →
  S._ConvergesTo_
    (λ n → Row.trianglePartial left right (Double.double n))
    (R._*_ (proj₁ leftConvergence) (proj₁ rightConvergence))
positiveCauchyEvenTriangleConverges
    left right leftNN rightNN leftConv rightConv =
  let
    leftLimit = proj₁ leftConv
    rightLimit = proj₁ rightConv
    rectangleConverges =
      Generic.rectangleConvergesToProduct
        left right leftLimit rightLimit
        (proj₂ leftConv) (proj₂ rightConv)
  in
  Squeeze.nativeBishopSqueeze
    (λ n → Rect.rectangleSum left right n n)
    (λ n → Row.trianglePartial left right (Double.double n))
    (λ n → Rect.rectangleSum left right
      (Double.double n) (Double.double n))
    (R._*_ leftLimit rightLimit)
    rectangleConverges
    (Double.doubleSubsequenceConverges rectangleConverges)
    (nonnegativeRectangleBelowEvenTriangle
      left right leftNN rightNN)
    (nonnegativeEvenTriangleBelowDoubleRectangle
      left right leftNN rightNN)

positiveCauchyTriangleConverges :
  (left right : Nat → R.ℝ) →
  (leftNonnegative : ∀ n → R.NonNegative (left n)) →
  (rightNonnegative : ∀ n → R.NonNegative (right n)) →
  (leftConvergence : S._isConvergent (S.SeriesOf left)) →
  (rightConvergence : S._isConvergent (S.SeriesOf right)) →
  S._ConvergesTo_
    (Row.trianglePartial left right)
    (R._*_ (proj₁ leftConvergence) (proj₁ rightConvergence))
positiveCauchyTriangleConverges
    left right leftNN rightNN leftConv rightConv =
  Monotone.monotoneDoubleConvergesImpliesFullConverges
    (Row.trianglePartial left right)
    (R._*_ (proj₁ leftConv) (proj₁ rightConv))
    (positiveCauchyTriangleIncreasing left right leftNN rightNN)
    (positiveCauchyEvenTriangleConverges
      left right leftNN rightNN leftConv rightConv)
