module DASHI.Moonshine.AbelBishopFactorialComplexExpDiskExact where

------------------------------------------------------------------------
-- ACTUAL BISHOP-COMPLEX FACTORIAL EXPONENTIAL SERIES ON THE UNIT DISK
--
-- We construct the positive-degree terms w^(n+1)/(n+1)! on the
-- original Bishop componentwise complex carrier, prove 1/n! <= 1
-- from the ALREADY-CHECKED Bishop exponential coefficient recurrence
-- and reciprocal order, and derive componentwise absolute convergence
-- by the existing geometric norm-square envelope.
--
-- This is NOT YET an identification of the series with
-- BishopSetoidComplexExact.expC T, nor an exp-log inverse theorem.
--
-- Every hypothesis is a genuine geometric radius witness. No
-- arbitrary "factorial coefficient bound" or convergence authority.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialPositiveOrderExact as ExpOrder
import DASHI.Foundations.BishopNegativeExponentialInterlacingExact as Reciprocal
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Moonshine.AbelBishopGeometricPowerSeriesExact as Powers
import DASHI.Moonshine.AbelBishopKoenigsGeometricAbsoluteExact as Geometric
import DASHI.Moonshine.AbelBishopLogOnePlusCoefficientDominationExact as Scalar

factorialCoefficient : Nat → BishopReal.ℝ
factorialCoefficient n = Exp.embed (Exp.inverseFactorial n)

factorialCoefficientZeroIsOne :
  BishopReal._≃_ (factorialCoefficient zero) BishopReal.1ℝ
factorialCoefficientZeroIsOne =
  BishopP.≃-trans
    (BishopP.≃-symm
      (BishopP.*-identityˡ (factorialCoefficient zero)))
    ExpOrder.expTermZeroAtZero

factorialCoefficientAtMostOne :
  ∀ n →
  BishopReal._≤_ (factorialCoefficient n) BishopReal.1ℝ
factorialCoefficientAtMostOne zero =
  BishopP.≤-reflexive factorialCoefficientZeroIsOne
factorialCoefficientAtMostOne (suc n) =
  BishopP.≤-trans
    (BishopP.≤-respˡ-≃
      (Exp.embeddedInverseFactorialSuccessor n)
      (BishopP.≤-respʳ-≃
        (BishopP.*-identityˡ (factorialCoefficient n))
        (BishopP.*-monoʳ-≤-nonNeg
          (Reciprocal.unitReciprocalBelowOne n)
          (Exp.embeddedInverseFactorialNonnegative n))))
    (factorialCoefficientAtMostOne n)

factorialCoefficientAbsoluteAtMostOne :
  ∀ n →
  BishopReal._≤_
    (BishopReal.∣ factorialCoefficient n ∣)
    BishopReal.1ℝ
factorialCoefficientAbsoluteAtMostOne n =
  BishopP.≤-respˡ-≃
    (BishopP.nonNegx⇒∣x∣≃x
      (BishopP.nonNegx⇒0≤x
        (Exp.embeddedInverseFactorialNonnegative n)))
    (factorialCoefficientAtMostOne n)

originalBishopFactorialExpPositiveTerm :
  Complex.BishopComplex → Nat → Complex.BishopComplex
originalBishopFactorialExpPositiveTerm w n =
  Algebra.scaleC
    (factorialCoefficient (suc n))
    (Algebra.powC w (suc n))

originalBishopFactorialExpPositiveRealBound :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (norm : BishopReal._≃_
    (Norm.normSqC w)
    (Norm.square ratio)) →
  ∀ n →
  BishopReal._≤_
    (BishopReal.∣ Complex.re
      (originalBishopFactorialExpPositiveTerm w n) ∣)
    (BishopReal._*_ ratio (BishopReal.pow ratio n))
originalBishopFactorialExpPositiveRealBound {w} interval norm n =
  BishopP.≤-trans
    (Scalar.originalBishopScalarMagnitudeAtMostOne
      (factorialCoefficient (suc n))
      (Complex.re (Powers.originalBishopGeometricPowerTerm w n))
      (factorialCoefficientAbsoluteAtMostOne (suc n)))
    (Geometric.realComponentBound
      (Powers.originalBishopPowerGeometricBounds interval norm) n)

originalBishopFactorialExpPositiveImagBound :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (norm : BishopReal._≃_
    (Norm.normSqC w)
    (Norm.square ratio)) →
  ∀ n →
  BishopReal._≤_
    (BishopReal.∣ Complex.im
      (originalBishopFactorialExpPositiveTerm w n) ∣)
    (BishopReal._*_ ratio (BishopReal.pow ratio n))
originalBishopFactorialExpPositiveImagBound {w} interval norm n =
  BishopP.≤-trans
    (Scalar.originalBishopScalarMagnitudeAtMostOne
      (factorialCoefficient (suc n))
      (Complex.im (Powers.originalBishopGeometricPowerTerm w n))
      (factorialCoefficientAbsoluteAtMostOne (suc n)))
    (Geometric.imaginaryComponentBound
      (Powers.originalBishopPowerGeometricBounds interval norm) n)

originalBishopFactorialExpPositiveBounds :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (norm : BishopReal._≃_
    (Norm.normSqC w)
    (Norm.square ratio)) →
  Geometric.OriginalBishopGeometricComponentBounds
    (originalBishopFactorialExpPositiveTerm w)
    ratio ratio
originalBishopFactorialExpPositiveBounds interval norm =
  record
    { geometricInputs = Powers.originalBishopPowerGeometricInputs interval
    ; realComponentBound =
        originalBishopFactorialExpPositiveRealBound interval norm
    ; imaginaryComponentBound =
        originalBishopFactorialExpPositiveImagBound interval norm
    }

originalBishopFactorialExpPositiveAbsoluteConvergence :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (norm : BishopReal._≃_
    (Norm.normSqC w)
    (Norm.square ratio)) →
  Complex.ComponentwiseAbsoluteSeriesConvergent
    (originalBishopFactorialExpPositiveTerm w)
originalBishopFactorialExpPositiveAbsoluteConvergence {w} {ratio} interval norm =
  Geometric.originalBishopKoenigsComponentAbsoluteSummability
    (originalBishopFactorialExpPositiveTerm w)
    ratio ratio
    (originalBishopFactorialExpPositiveBounds interval norm)

originalBishopFactorialExpPositiveLimit :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (norm : BishopReal._≃_
    (Norm.normSqC w)
    (Norm.square ratio)) →
  Complex.BishopComplex
originalBishopFactorialExpPositiveLimit {w} interval norm =
  Complex.complexSeriesLimit
    (originalBishopFactorialExpPositiveTerm w)
    (originalBishopFactorialExpPositiveAbsoluteConvergence interval norm)

originalBishopFactorialExpPositiveLimitConverges :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (norm : BishopReal._≃_
    (Norm.normSqC w)
    (Norm.square ratio)) →
  Complex.ComplexSeriesConvergesTo
    (originalBishopFactorialExpPositiveTerm w)
    (originalBishopFactorialExpPositiveLimit interval norm)
originalBishopFactorialExpPositiveLimitConverges {w} interval norm =
  Complex.complexSeriesLimitConvergence
    (originalBishopFactorialExpPositiveTerm w)
    (originalBishopFactorialExpPositiveAbsoluteConvergence interval norm)

-- The intended complete factorial series value, from its canonical
-- positive-degree limit plus the original complex multiplicative unit.
originalBishopFactorialExpDiskValue :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (norm : BishopReal._≃_
    (Norm.normSqC w)
    (Norm.square ratio)) →
  Complex.BishopComplex
originalBishopFactorialExpDiskValue interval norm =
  Algebra._+C_ Algebra.oneC
    (originalBishopFactorialExpPositiveLimit interval norm)
