module DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact where

------------------------------------------------------------------------
-- TERMINAL CONSTRUCTIVE E4/E6 q-SERIES THEOREM ON THE BISHOP UNIT DISK
--
-- DASHI CONTRIBUTION
--
-- This is the preferred analytic endpoint for the current #999 convergence
-- programme.  It does not require a legacy ConcreteComplex quotient and it
-- does not require a particular tau -> q parametrisation.
--
-- For any concrete Bishop complex q equipped with a radius r satisfying
--
--   0 <= r < 1
--   normSq(q) ~= r^2,
--
-- the concrete Bishop square-order theorem turns normSq multiplicativity into
-- componentwise power bounds.  Existing exact divisor arithmetic and the
-- polynomial/geometric comparison theorem then construct canonical Bishop
-- complex limits for the classical divisor-sum E4/E6 q-series.
--
-- The separate theorem q(tau)=exp(2*pi*i*tau) is a parameterisation/same-object
-- theorem, not a convergence premise.
------------------------------------------------------------------------

import Real as BishopReal

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Foundations.BishopNonnegativeSquareReflectionExact as SquareReflection
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as Eisenstein

record BishopUnitDiskQ
    (q : Complex.BishopComplex)
    (ratio : BishopReal.ℝ) : Set₁ where
  field
    unitInterval : Unit.BishopUnitIntervalRatio ratio
    normSquareAgreement :
      BishopReal._≃_
        (Norm.normSqC q)
        (Norm.square ratio)

open BishopUnitDiskQ public

powerEnvelope :
  ∀ {q ratio} →
  BishopUnitDiskQ q ratio →
  Norm.BishopQPowerComponentEnvelope q ratio
powerEnvelope {q} {ratio} input =
  Norm.powerEnvelopeFromNormSquare
    q
    SquareReflection.bishopNonnegativeSquareReflection
    (BishopReal.0≤x⇒nonNegx (Unit.ratioNonnegative (unitInterval input)))
    (normSquareAgreement input)

record BishopUnitDiskEisensteinCompletion
    (q : Complex.BishopComplex)
    (ratio : BishopReal.ℝ)
    (input : BishopUnitDiskQ q ratio) : Set₁ where
  field
    qPowerEnvelope :
      Norm.BishopQPowerComponentEnvelope q ratio

    e4AbsoluteConvergence :
      Complex.ComponentwiseAbsoluteSeriesConvergent
        (Eisenstein.e4BishopTerm q)

    e6AbsoluteConvergence :
      Complex.ComponentwiseAbsoluteSeriesConvergent
        (Eisenstein.e6BishopUnsignedTerm q)

    e4Limit : Complex.BishopComplex
    e6Limit : Complex.BishopComplex

    e4Converges :
      Complex.ComplexSeriesConvergesTo
        (Eisenstein.e4BishopTerm q)
        (Eisenstein.e4BishopTailLimit
          q (unitInterval input) qPowerEnvelope)

    e6Converges :
      Complex.ComplexSeriesConvergesTo
        (Eisenstein.e6BishopUnsignedTerm q)
        (Eisenstein.e6BishopUnsignedTailLimit
          q (unitInterval input) qPowerEnvelope)

    e4Canonical :
      Complex._≈C_
        e4Limit
        (Eisenstein.e4BishopLimit
          q (unitInterval input) qPowerEnvelope)

    e6Canonical :
      Complex._≈C_
        e6Limit
        (Eisenstein.e6BishopLimit
          q (unitInterval input) qPowerEnvelope)

open BishopUnitDiskEisensteinCompletion public

completeBishopUnitDiskEisenstein :
  ∀ {q ratio} →
  (input : BishopUnitDiskQ q ratio) →
  BishopUnitDiskEisensteinCompletion q ratio input
completeBishopUnitDiskEisenstein {q} {ratio} input =
  let
    envelope = powerEnvelope input
    unit = unitInterval input
  in
  record
    { qPowerEnvelope = envelope
    ; e4AbsoluteConvergence =
        Eisenstein.e4BishopComponentwiseAbsoluteConvergence
          q unit envelope
    ; e6AbsoluteConvergence =
        Eisenstein.e6BishopComponentwiseAbsoluteConvergence
          q unit envelope
    ; e4Limit =
        Eisenstein.e4BishopLimit q unit envelope
    ; e6Limit =
        Eisenstein.e6BishopLimit q unit envelope
    ; e4Converges =
        Eisenstein.e4BishopTailConvergence q unit envelope
    ; e6Converges =
        Eisenstein.e6BishopUnsignedTailConvergence q unit envelope
    ; e4Canonical = Complex.≈C-refl
    ; e6Canonical = Complex.≈C-refl
    }
