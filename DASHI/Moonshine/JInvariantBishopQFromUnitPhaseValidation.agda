module DASHI.Moonshine.JInvariantBishopQFromUnitPhaseValidation where

import Real as BishopReal

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as Eisenstein
import DASHI.Moonshine.JInvariantBishopQFromUnitPhaseExact as P

qRadiusCertificateRegression :
  ∀ (phase : Complex.BishopComplex)
    {ratio : BishopReal.ℝ} →
  BishopReal._≃_ (Norm.normSqC phase) BishopReal.1ℝ →
  BishopReal.NonNegative ratio →
  Norm.BishopQNormSquareRadius
    (P.qFromRadiusAndPhase ratio phase)
    ratio
qRadiusCertificateRegression =
  P.qNormSquareRadiusFromUnitPhase

qEnvelopeRegression :
  ∀ (phase : Complex.BishopComplex)
    {ratio : BishopReal.ℝ} →
  BishopReal._≃_ (Norm.normSqC phase) BishopReal.1ℝ →
  Unit.BishopUnitIntervalRatio ratio →
  Norm.BishopNonnegativeSquareReflection →
  Norm.BishopQPowerComponentEnvelope
    (P.qFromRadiusAndPhase ratio phase)
    ratio
qEnvelopeRegression =
  P.qPowerEnvelopeFromUnitPhase

e4LimitRegression :
  ∀ (phase : Complex.BishopComplex)
    {ratio : BishopReal.ℝ}
    (phaseUnit : BishopReal._≃_ (Norm.normSqC phase) BishopReal.1ℝ)
    (unit : Unit.BishopUnitIntervalRatio ratio)
    (reflection : Norm.BishopNonnegativeSquareReflection) →
  Complex.BishopComplex
e4LimitRegression =
  P.e4LimitFromUnitPhase

e6LimitRegression :
  ∀ (phase : Complex.BishopComplex)
    {ratio : BishopReal.ℝ}
    (phaseUnit : BishopReal._≃_ (Norm.normSqC phase) BishopReal.1ℝ)
    (unit : Unit.BishopUnitIntervalRatio ratio)
    (reflection : Norm.BishopNonnegativeSquareReflection) →
  Complex.BishopComplex
e6LimitRegression =
  P.e6LimitFromUnitPhase
