module DASHI.Moonshine.JInvariantBishopUpperHalfPlaneEisensteinFromUnitPhaseValidation where

import Real as BishopReal

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Moonshine.JInvariantBishopTrigUnitPhaseExact as Trig
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneEisensteinFromUnitPhaseExact as P

e4UpperHalfPlaneLimitRegression :
  ∀ (phase : Complex.BishopComplex)
    {piB imagB : BishopReal.ℝ}
    (phaseUnit : BishopReal._≃_ (Norm.normSqC phase) BishopReal.1ℝ)
    (piPositive : BishopReal._<_ BishopReal.0ℝ piB)
    (imagPositive : BishopReal._<_ BishopReal.0ℝ imagB)
    (reflection : Norm.BishopNonnegativeSquareReflection) →
  Complex.BishopComplex
e4UpperHalfPlaneLimitRegression =
  P.e4UpperHalfPlaneLimitFromUnitPhase

e6UpperHalfPlaneLimitRegression :
  ∀ (phase : Complex.BishopComplex)
    {piB imagB : BishopReal.ℝ}
    (phaseUnit : BishopReal._≃_ (Norm.normSqC phase) BishopReal.1ℝ)
    (piPositive : BishopReal._<_ BishopReal.0ℝ piB)
    (imagPositive : BishopReal._<_ BishopReal.0ℝ imagB)
    (reflection : Norm.BishopNonnegativeSquareReflection) →
  Complex.BishopComplex
e6UpperHalfPlaneLimitRegression =
  P.e6UpperHalfPlaneLimitFromUnitPhase


trigE4UpperHalfPlaneLimitRegression :
  (dataSet : Elementary.BishopElementaryPowerSeriesData) →
  (angle : BishopReal.ℝ) →
  (pythagorean : Trig.BishopTrigPythagoreanAt dataSet angle) →
  ∀ {piB imagB : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ piB →
  BishopReal._<_ BishopReal.0ℝ imagB →
  Norm.BishopNonnegativeSquareReflection →
  Complex.BishopComplex
trigE4UpperHalfPlaneLimitRegression =
  P.e4UpperHalfPlaneLimitFromTrigPhase

trigE6UpperHalfPlaneLimitRegression :
  (dataSet : Elementary.BishopElementaryPowerSeriesData) →
  (angle : BishopReal.ℝ) →
  (pythagorean : Trig.BishopTrigPythagoreanAt dataSet angle) →
  ∀ {piB imagB : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ piB →
  BishopReal._<_ BishopReal.0ℝ imagB →
  Norm.BishopNonnegativeSquareReflection →
  Complex.BishopComplex
trigE6UpperHalfPlaneLimitRegression =
  P.e6UpperHalfPlaneLimitFromTrigPhase
