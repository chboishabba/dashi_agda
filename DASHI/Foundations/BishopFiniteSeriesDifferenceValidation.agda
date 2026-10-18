module DASHI.Foundations.BishopFiniteSeriesDifferenceValidation where

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Foundations.BishopFiniteSeriesDifferenceExact as P

finiteSeriesDifferenceRegression :
  (left right : Nat → BishopReal.ℝ) →
  ∀ count →
  BishopReal._≃_
    (BishopReal._-_
      (BishopSequence.SeriesOf left count)
      (BishopSequence.SeriesOf right count))
    (BishopSequence.SeriesOf
      (λ index → BishopReal._-_ (left index) (right index))
      count)
finiteSeriesDifferenceRegression =
  P.finiteSeriesDifference
