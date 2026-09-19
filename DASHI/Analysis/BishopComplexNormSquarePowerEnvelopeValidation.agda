module DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeValidation where

import Real as BishopReal

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
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

unitPhaseScaledNormSquareRegression :
  ∀ {phase ratio} →
  BishopReal._≃_ (P.normSqC phase) BishopReal.1ℝ →
  BishopReal._≃_
    (P.normSqC
      (Algebra.scaleC ratio phase))
    (BishopReal._*_ ratio ratio)
unitPhaseScaledNormSquareRegression =
  P.unitPhaseScaledNormSquare
