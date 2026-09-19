module DASHI.Foundations.BishopFiniteCauchyTriangleInsideRectangleExact where

------------------------------------------------------------------------
-- NONNEGATIVE CAUCHY TRIANGLE SITS INSIDE THE MATCHING SQUARE
--
-- DASHI CONTRIBUTION
--
-- For nonnegative terms,
--
--   T_N(a,b) <= R_{N,N}(a,b).
--
-- The existing reverse-scale theorem already gives
--
--   R_{N,N}(a,b) <= T_{2N}(a,b).
--
-- Together these bracket the positive square wing by the positive Cauchy tail.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as NatP

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Foundations.BishopFiniteSeriesRectangleProductExact as Rectangle
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopFiniteRectangleInsideCauchyTriangleExact as Existing

triangleRowsBelowSquareRows :
  ∀ {left right : Nat → BishopReal.ℝ} →
  (leftNonnegative : ∀ index → BishopReal.NonNegative (left index)) →
  (rightNonnegative : ∀ index → BishopReal.NonNegative (right index)) →
  ∀ count →
  BishopReal._≤_
    (BishopSequence.SeriesOf
      (Existing.triangleRow left right count)
      count)
    (Existing.rectangleNativeRows left right count count)
triangleRowsBelowSquareRows
    {left} {right} leftNonnegative rightNonnegative count =
  Existing.finitePointwiseBound count
    (λ index index<count →
      BishopP.*-monoˡ-≤-nonNeg
        (Existing.finPrefixMonotone
          rightNonnegative
          (NatP.m∸n≤m count index))
        (leftNonnegative index))

triangleInsideSquare :
  ∀ {left right : Nat → BishopReal.ℝ} →
  (leftNonnegative : ∀ index → BishopReal.NonNegative (left index)) →
  (rightNonnegative : ∀ index → BishopReal.NonNegative (right index)) →
  ∀ count →
  BishopReal._≤_
    (Row.trianglePartial left right count)
    (Rectangle.rectangleSum left right count count)
triangleInsideSquare
    {left} {right} leftNonnegative rightNonnegative count =
  BishopP.≤-respʳ-≃
    (BishopP.≃-symm
      (Existing.rectangleSumIsNativeRows
        left right count count))
    (BishopP.≤-respˡ-≃
      (BishopP.≃-trans
        (Row.triangleIsMertensRow left right count)
        (Existing.allRowsIsMertensRow left right count))
      (triangleRowsBelowSquareRows
        leftNonnegative rightNonnegative count))
