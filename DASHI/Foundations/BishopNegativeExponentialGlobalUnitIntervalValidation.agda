module DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalValidation where

import Real as BishopReal
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact as P

negativeExpPositiveRegression :
  ∀ {x} →
  BishopReal._<_ BishopReal.0ℝ x →
  BishopReal._<_
    BishopReal.0ℝ
    (Exp.bishopExp (BishopReal.- x))
negativeExpPositiveRegression = P.negativeExpPositive

negativeExpBelowOneRegression :
  ∀ {x} →
  BishopReal._<_ BishopReal.0ℝ x →
  BishopReal._<_
    (Exp.bishopExp (BishopReal.- x))
    BishopReal.1ℝ
negativeExpBelowOneRegression = P.negativeExpBelowOne
