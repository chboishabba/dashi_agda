module DASHI.Foundations.BishopFiniteCauchyTriangleInsideRectangleValidation where

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal

import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopFiniteSeriesRectangleProductExact as Rectangle
import DASHI.Foundations.BishopFiniteCauchyTriangleInsideRectangleExact as P

triangleInsideSquareRegression :
  ∀ {left right : Nat → BishopReal.ℝ} →
  (∀ index → BishopReal.NonNegative (left index)) →
  (∀ index → BishopReal.NonNegative (right index)) →
  ∀ count →
  BishopReal._≤_
    (Row.trianglePartial left right count)
    (Rectangle.rectangleSum left right count count)
triangleInsideSquareRegression =
  P.triangleInsideSquare
