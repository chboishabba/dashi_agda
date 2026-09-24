module DASHI.Moonshine.JInvariantBishopQFromUnitPhaseExact where

------------------------------------------------------------------------
-- BISHOP q FROM RADIUS × UNIT PHASE
--
-- DASHI CONTRIBUTION
--
-- The preferred setoid-native convergence route does not need a global
-- trigonometric package.  It needs only one Bishop complex q with a power
-- component envelope against a scalar radius r in [0,1).
--
-- This owner factors that input:
--
--   q = r * phase
--   normSq(phase) ~= 1
--
-- gives
--
--   normSq(q) ~= r^2.
--
-- Combined with the already-owned normSq-power propagation and one generic
-- nonnegative square-order reflection capability, this produces the entire
-- all-n component-power envelope consumed by the Bishop E4/E6 series owner.
--
-- Thus phase construction / Pythagorean semantics remain a separate producer;
-- no sine/cosine theorem is imported into the convergence proof.
------------------------------------------------------------------------

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as Eisenstein

qFromRadiusAndPhase :
  BishopReal.ℝ →
  Complex.BishopComplex →
  Complex.BishopComplex
qFromRadiusAndPhase ratio phase =
  Algebra.scaleC ratio phase

qNormSquareRadiusFromUnitPhase :
  ∀ (phase : Complex.BishopComplex)
    {ratio : BishopReal.ℝ} →
  BishopReal._≃_ (Norm.normSqC phase) BishopReal.1ℝ →
  BishopReal.NonNegative ratio →
  Norm.BishopQNormSquareRadius
    (qFromRadiusAndPhase ratio phase)
    ratio
qNormSquareRadiusFromUnitPhase phase {ratio} phaseUnit ratioNN = record
  { Norm.ratioNonnegative = ratioNN
  ; Norm.normSquareAgreement =
      Norm.unitPhaseScaledNormSquare phaseUnit
  }

qPowerEnvelopeFromUnitPhase :
  ∀ (phase : Complex.BishopComplex)
    {ratio : BishopReal.ℝ} →
  BishopReal._≃_ (Norm.normSqC phase) BishopReal.1ℝ →
  Unit.BishopUnitIntervalRatio ratio →
  Norm.BishopNonnegativeSquareReflection →
  Norm.BishopQPowerComponentEnvelope
    (qFromRadiusAndPhase ratio phase)
    ratio
qPowerEnvelopeFromUnitPhase phase {ratio} phaseUnit unit reflection =
  Norm.powerEnvelopeFromNormSquare
    (qFromRadiusAndPhase ratio phase)
    reflection
    (BishopP.0≤x⇒nonNegx (Unit.ratioNonnegative unit))
    (Norm.normSquareAgreement
      (qNormSquareRadiusFromUnitPhase
        phase
        phaseUnit
        (BishopP.0≤x⇒nonNegx (Unit.ratioNonnegative unit))))

e4LimitFromUnitPhase :
  ∀ (phase : Complex.BishopComplex)
    {ratio : BishopReal.ℝ}
    (phaseUnit : BishopReal._≃_ (Norm.normSqC phase) BishopReal.1ℝ)
    (unit : Unit.BishopUnitIntervalRatio ratio)
    (reflection : Norm.BishopNonnegativeSquareReflection) →
  Complex.BishopComplex
e4LimitFromUnitPhase phase {ratio} phaseUnit unit reflection =
  Eisenstein.e4BishopLimit
    (qFromRadiusAndPhase ratio phase)
    unit
    (qPowerEnvelopeFromUnitPhase phase phaseUnit unit reflection)

e6LimitFromUnitPhase :
  ∀ (phase : Complex.BishopComplex)
    {ratio : BishopReal.ℝ}
    (phaseUnit : BishopReal._≃_ (Norm.normSqC phase) BishopReal.1ℝ)
    (unit : Unit.BishopUnitIntervalRatio ratio)
    (reflection : Norm.BishopNonnegativeSquareReflection) →
  Complex.BishopComplex
e6LimitFromUnitPhase phase {ratio} phaseUnit unit reflection =
  Eisenstein.e6BishopLimit
    (qFromRadiusAndPhase ratio phase)
    unit
    (qPowerEnvelopeFromUnitPhase phase phaseUnit unit reflection)
