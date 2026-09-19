module DASHI.Analysis.BishopPolynomialGeometricSeriesConvergenceValidation where

open import Agda.Builtin.Nat using (Nat; suc)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Analysis.BishopPolynomialGeometricSeriesConvergenceExact as P

successorFactorizationRegression :
  ∀ (ratio : BishopReal.ℝ) degree index →
  BishopReal._≃_
    (P.polynomialGeometricTerm ratio degree (suc (suc index)))
    (BishopReal._*_
      (P.successorFactor ratio degree index)
      (P.polynomialGeometricTerm ratio degree (suc index)))
successorFactorizationRegression =
  P.polynomialGeometricSuccessorFactorization

fixedDegreeConvergenceRegression :
  ∀ (ratio : BishopReal.ℝ) degree →
  BishopReal._≤_ BishopReal.0ℝ ratio →
  BishopReal._<_ ratio BishopReal.1ℝ →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf
      (P.polynomialGeometricTerm ratio degree))
fixedDegreeConvergenceRegression =
  P.polynomialGeometricSeriesConvergent
