module DASHI.Moonshine.AbelBishopGeometricPowerSeriesExact where

------------------------------------------------------------------------
-- ACTUAL BISHOP COMPLEX GEOMETRIC-POWER SERIES.
--
-- Given one norm-square radius certificate (|w| = r, 0 <= r < 1),
-- prove absolute componentwise convergence of the actual terms
--     w^(n+1)     for every n : Nat,
-- by using the existing norm-square power envelope and the
-- already-paid Bishop geometric comparison backend.
--
-- This is NOT a logarithm identity. Multiplication by
-- (-1)^n/(n+1) and original principal-log branch identification
-- remain separate unpaid producer theorems.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Foundations.BishopNonnegativeSquareReflectionExact as Reflection
import DASHI.Moonshine.AbelBishopKoenigsGeometricAbsoluteExact as Geometric
import DASHI.Foundations.BishopPolynomialGeometricDominationConvergenceExact as Geom

originalBishopGeometricPowerTerm :
  Complex.BishopComplex → Nat → Complex.BishopComplex
originalBishopGeometricPowerTerm w n =
  Algebra.powC w (suc n)

originalBishopPowerEnvelopeFromRadius :
  ∀ {w ratio} →
  Unit.BishopUnitIntervalRatio ratio →
  BishopReal._≃_
    (Norm.normSqC w)
    (Norm.square ratio) →
  Norm.BishopQPowerComponentEnvelope w ratio
originalBishopPowerEnvelopeFromRadius {w} {ratio} interval norm =
  Norm.powerEnvelopeFromNormSquare
    w
    Reflection.bishopNonnegativeSquareReflection
    (BishopP.0≤x⇒nonNegx (Unit.ratioNonnegative interval))
    norm

originalBishopPowerGeometricInputs :
  ∀ {ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  Geom.BishopScaledGeometricInputs ratio ratio
originalBishopPowerGeometricInputs {ratio} interval =
  record
    { constantNonnegative = Unit.ratioNonnegative interval
    ; ratioInputs = interval
    }

originalBishopPowerGeometricBounds :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  BishopReal._≃_
    (Norm.normSqC w)
    (Norm.square ratio) →
  Geometric.OriginalBishopGeometricComponentBounds
    (originalBishopGeometricPowerTerm w)
    ratio
    ratio
originalBishopPowerGeometricBounds {w} {ratio} interval norm =
  record
    { geometricInputs = originalBishopPowerGeometricInputs interval
    ; realComponentBound = Norm.realPowerBound envelope
    ; imaginaryComponentBound = Norm.imagPowerBound envelope
    }
  where
    envelope : Norm.BishopQPowerComponentEnvelope w ratio
    envelope = originalBishopPowerEnvelopeFromRadius interval norm

originalBishopGeometricPowerAbsoluteConvergence :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  BishopReal._≃_
    (Norm.normSqC w)
    (Norm.square ratio) →
  Complex.ComponentwiseAbsoluteSeriesConvergent
    (originalBishopGeometricPowerTerm w)
originalBishopGeometricPowerAbsoluteConvergence {w} {ratio} interval norm =
  Geometric.originalBishopKoenigsComponentAbsoluteSummability
    (originalBishopGeometricPowerTerm w)
    ratio
    ratio
    (originalBishopPowerGeometricBounds interval norm)

originalBishopGeometricPowerLimit :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  BishopReal._≃_
    (Norm.normSqC w)
    (Norm.square ratio) →
  Complex.BishopComplex
originalBishopGeometricPowerLimit {w} {ratio} interval norm =
  Complex.complexSeriesLimit
    (originalBishopGeometricPowerTerm w)
    (originalBishopGeometricPowerAbsoluteConvergence interval norm)
