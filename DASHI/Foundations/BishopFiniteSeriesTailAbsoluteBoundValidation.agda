module DASHI.Foundations.BishopFiniteSeriesTailAbsoluteBoundValidation where

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Foundations.BishopFiniteSeriesTailAbsoluteBoundExact as P

finiteTailAbsoluteBoundRegression :
  (terms : Nat → BishopReal.ℝ) →
  ∀ start count →
  BishopReal._≤_
    (BishopReal.∣
      BishopReal._-_
        (BishopSequence.SeriesOf terms (start + count))
        (BishopSequence.SeriesOf terms start)
    ∣)
    (BishopReal._-_
      (BishopSequence.SeriesOf
        (λ index → BishopReal.∣ terms index ∣)
        (start + count))
      (BishopSequence.SeriesOf
        (λ index → BishopReal.∣ terms index ∣)
        start))
finiteTailAbsoluteBoundRegression =
  P.finiteTailAbsoluteBound
