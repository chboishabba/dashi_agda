module DASHI.Analysis.BishopGeometricMajorantSeriesConvergenceValidation where

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Analysis.BishopGeometricMajorantSeriesConvergenceExact as P

geometricMajorantRegression :
  ∀ (ratio scale : BishopReal.ℝ) →
  BishopReal._<_ BishopReal.0ℝ ratio →
  BishopReal._<_ ratio BishopReal.1ℝ →
  BishopReal.NonNegative scale →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf (P.scaledGeometricTerm scale ratio))
geometricMajorantRegression = P.scaledGeometricSeriesConvergent

comparisonRegression :
  ∀ (terms : Nat → BishopReal.ℝ)
    (ratio scale : BishopReal.ℝ) →
  BishopReal._<_ BishopReal.0ℝ ratio →
  BishopReal._<_ ratio BishopReal.1ℝ →
  BishopReal.NonNegative scale →
  (∀ index →
    BishopReal._≤_
      (BishopReal.∣_∣ (terms index))
      (P.scaledGeometricTerm scale ratio index)) →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf terms)
comparisonRegression = P.seriesConvergentFromScaledGeometricMajorant
