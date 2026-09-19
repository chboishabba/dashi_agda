module DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeValidation where

import Real as BishopReal

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as P

normSquareMultiplicationRegression :
  ∀ left right →
  BishopReal._≃_
    (P.normSqC (P._*C_ left right))
    (BishopReal._*_ (P.normSqC left) (P.normSqC right))
normSquareMultiplicationRegression =
  P.normSqMultiply

powerEnvelopeRegression :
  ∀ (q : Complex.BishopComplex) {ratio} →
  P.BishopNonnegativeSquareReflection →
  BishopReal.NonNegative ratio →
  BishopReal._≃_
    (P.normSqC q)
    (BishopReal._*_ ratio ratio) →
  P.BishopQPowerComponentEnvelope q ratio
powerEnvelopeRegression =
  P.powerEnvelopeFromNormSquare
