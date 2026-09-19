module DASHI.Foundations.BishopFiniteCauchyWingAbsoluteBoundValidation where

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import DASHI.Foundations.BishopFiniteSeriesRectangleProductExact as Rectangle
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopFiniteCauchyWingAbsoluteBoundExact as P

wingAbsoluteBoundRegression :
  (left right : Nat → BishopReal.ℝ) →
  ∀ count →
  BishopReal._≤_
    (BishopReal.∣
      BishopReal._-_
        (Rectangle.rectangleSum left right count count)
        (Row.trianglePartial left right count)
    ∣)
    (BishopReal._-_
      (Row.trianglePartial
        (λ index → BishopReal.∣ left index ∣)
        (λ index → BishopReal.∣ right index ∣)
        (count + count))
      (Row.trianglePartial
        (λ index → BishopReal.∣ left index ∣)
        (λ index → BishopReal.∣ right index ∣)
        count))
wingAbsoluteBoundRegression = P.finiteCauchyWingAbsoluteBound
