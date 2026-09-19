module DASHI.Foundations.BishopFiniteSeriesAbsoluteBoundValidation where

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Foundations.BishopFiniteSeriesAbsoluteBoundExact as P

finiteSeriesAbsoluteBoundRegression :
  (terms : Nat → BishopReal.ℝ) →
  ∀ count →
  BishopReal._≤_
    (BishopReal.∣ BishopSequence.SeriesOf terms count ∣)
    (BishopSequence.SeriesOf
      (λ index → BishopReal.∣ terms index ∣)
      count)
finiteSeriesAbsoluteBoundRegression =
  P.finiteSeriesAbsoluteBound
