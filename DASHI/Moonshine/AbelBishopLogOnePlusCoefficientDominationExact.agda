module DASHI.Moonshine.AbelBishopLogOnePlusCoefficientDominationExact where

------------------------------------------------------------------------
-- SOURCE-NATIVE LOG SERIES COMPARISON, WITH ONLY FINITE RATIONAL
-- COEFFICIENT ORDER LEFT OPEN.
--
-- Actual log terms: (-1)^n/(n+1) * w^(n+1).
-- The hard-coded coefficient is NOT replaced by a separate chosen
-- sequence or a purported principal logarithm authority.
--
-- Inputs: a selected Bishop unit-disk radius and the single scalar
-- arithmetic inequality |(-1)^n/(n+1)| <= 1 for every Nat n.
--
-- Output: Bishop componentwise absolute convergence of precisely
-- those source terms via norm-square power envelope and the existing
-- geometric comparison backend.
--
-- OPEN: derive the coefficient inequality from literal rational
-- arithmetic, then prove principal-branch identity on original disk.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_,_)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Moonshine.AbelBishopKoenigsGeometricAbsoluteExact as Geom
import DASHI.Moonshine.AbelBishopGeometricPowerSeriesExact as Powers
import DASHI.Moonshine.AbelBishopLogOnePlusOriginalSeriesExact as Log
import DASHI.Foundations.BishopNegativeExponentialInterlacingExact as Reciprocal

originalBishopScalarMagnitudeAtMostOne :
  (scalar x : BishopReal.ℝ) →
  BishopReal._≤_ (BishopReal.∣ scalar ∣) BishopReal.1ℝ →
  BishopReal._≤_
    (BishopReal.∣ BishopReal._*_ scalar x ∣)
    (BishopReal.∣ x ∣)
originalBishopScalarMagnitudeAtMostOne scalar x bound =
  BishopP.≤-respˡ-≃
    (BishopP.∣x*y∣≃∣x∣*∣y∣ scalar x)
    (BishopP.≤-respʳ-≃
      (BishopP.*-identityˡ (BishopReal.∣ x ∣))
      (BishopP.*-monoʳ-≤-nonNeg
        bound
        (BishopP.nonNeg∣x∣ x)))

originalBishopLogRealComponentBelowGeometric :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (norm : BishopReal._≃_
    (Norm.normSqC w)
    (Norm.square ratio)) →
  (coefficientBound : ∀ n →
    BishopReal._≤_
      (BishopReal.∣ Log.logCoefficient n ∣)
      BishopReal.1ℝ) →
  ∀ n →
  BishopReal._≤_
    (BishopReal.∣ Complex.re (Log.originalBishopLogOnePlusTerm w n) ∣)
    (BishopReal._*_
      ratio
      (BishopReal.pow ratio n))
originalBishopLogRealComponentBelowGeometric {w} interval norm coefficientBound n =
  BishopP.≤-trans
    (originalBishopScalarMagnitudeAtMostOne
      (Log.logCoefficient n)
      (Complex.re (Powers.originalBishopGeometricPowerTerm w n))
      (coefficientBound n))
    (Geom.realComponentBound
      (Powers.originalBishopPowerGeometricBounds interval norm) n)

originalBishopLogImagComponentBelowGeometric :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (norm : BishopReal._≃_
    (Norm.normSqC w)
    (Norm.square ratio)) →
  (coefficientBound : ∀ n →
    BishopReal._≤_
      (BishopReal.∣ Log.logCoefficient n ∣)
      BishopReal.1ℝ) →
  ∀ n →
  BishopReal._≤_
    (BishopReal.∣ Complex.im (Log.originalBishopLogOnePlusTerm w n) ∣)
    (BishopReal._*_
      ratio
      (BishopReal.pow ratio n))
originalBishopLogImagComponentBelowGeometric {w} interval norm coefficientBound n =
  BishopP.≤-trans
    (originalBishopScalarMagnitudeAtMostOne
      (Log.logCoefficient n)
      (Complex.im (Powers.originalBishopGeometricPowerTerm w n))
      (coefficientBound n))
    (Geom.imaginaryComponentBound
      (Powers.originalBishopPowerGeometricBounds interval norm) n)

originalBishopLogComponentGeometricBounds :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (norm : BishopReal._≃_
    (Norm.normSqC w)
    (Norm.square ratio)) →
  (coefficientBound : ∀ n →
    BishopReal._≤_
      (BishopReal.∣ Log.logCoefficient n ∣)
      BishopReal.1ℝ) →
  Geom.OriginalBishopGeometricComponentBounds
    (Log.originalBishopLogOnePlusTerm w)
    ratio
    ratio
originalBishopLogComponentGeometricBounds interval norm coefficientBound =
  record
    { geometricInputs = Powers.originalBishopPowerGeometricInputs interval
    ; realComponentBound =
        originalBishopLogRealComponentBelowGeometric interval norm coefficientBound
    ; imaginaryComponentBound =
        originalBishopLogImagComponentBelowGeometric interval norm coefficientBound
    }

originalBishopLogOnePlusAbsoluteFromCoefficientOrder :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (norm : BishopReal._≃_
    (Norm.normSqC w)
    (Norm.square ratio)) →
  (coefficientBound : ∀ n →
    BishopReal._≤_
      (BishopReal.∣ Log.logCoefficient n ∣)
      BishopReal.1ℝ) →
  Complex.ComponentwiseAbsoluteSeriesConvergent
    (Log.originalBishopLogOnePlusTerm w)
originalBishopLogOnePlusAbsoluteFromCoefficientOrder {w} {ratio} interval norm coefficientBound =
  Geom.originalBishopKoenigsComponentAbsoluteSummability
    (Log.originalBishopLogOnePlusTerm w)
    ratio
    ratio
    (originalBishopLogComponentGeometricBounds interval norm coefficientBound)


------------------------------------------------------------------------
-- PAY THE REMAINING COEFFICIENT ORDER FROM ORIGINAL VENDORED
-- BISHOP RATIONAL RECIPROCAL PRIOR ART. NO INPUT FIELD REMAINS.
------------------------------------------------------------------------

originalBishopLogCoefficientMagnitudeAtMostOne :
  ∀ n →
  BishopReal._≤_
    (BishopReal.∣ Log.logCoefficient n ∣)
    BishopReal.1ℝ
originalBishopLogCoefficientMagnitudeAtMostOne n
  with Log.alternate n
... | false =
  BishopP.≤-respˡ-≃
    (BishopP.nonNegx⇒∣x∣≃x
      (Reciprocal.reciprocalNonnegative n))
    (Reciprocal.unitReciprocalBelowOne n)
... | true =
  BishopP.≤-respˡ-≃
    (BishopP.≃-trans
      BishopP.∣-x∣≃∣x∣
      (BishopP.nonNegx⇒∣x∣≃x
        (Reciprocal.reciprocalNonnegative n)))
    (Reciprocal.unitReciprocalBelowOne n)

-- This discharges the literal log-term absolute convergence from a
-- source-selected norm-square radius and the *existing* Bishop geometric
-- comparison; no arbitrary coefficient-order record is required.
originalBishopLogOnePlusAbsoluteConvergenceOnUnitDisk :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (norm : BishopReal._≃_
    (Norm.normSqC w)
    (Norm.square ratio)) →
  Complex.ComponentwiseAbsoluteSeriesConvergent
    (Log.originalBishopLogOnePlusTerm w)
originalBishopLogOnePlusAbsoluteConvergenceOnUnitDisk interval norm =
  originalBishopLogOnePlusAbsoluteFromCoefficientOrder
    interval norm originalBishopLogCoefficientMagnitudeAtMostOne

originalBishopLogOnePlusCanonicalLimitOnUnitDisk :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (norm : BishopReal._≃_
    (Norm.normSqC w)
    (Norm.square ratio)) →
  Complex.BishopComplex
originalBishopLogOnePlusCanonicalLimitOnUnitDisk {w} interval norm =
  Log.originalBishopLogOnePlusSeriesValue w
    (originalBishopLogOnePlusAbsoluteConvergenceOnUnitDisk interval norm)

originalBishopLogOnePlusCanonicalLimitConvergesOnUnitDisk :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (norm : BishopReal._≃_
    (Norm.normSqC w)
    (Norm.square ratio)) →
  Complex.ComplexSeriesConvergesTo
    (Log.originalBishopLogOnePlusTerm w)
    (originalBishopLogOnePlusCanonicalLimitOnUnitDisk interval norm)
originalBishopLogOnePlusCanonicalLimitConvergesOnUnitDisk {w} interval norm =
  Log.originalBishopLogOnePlusSeriesConverges w
    (originalBishopLogOnePlusAbsoluteConvergenceOnUnitDisk interval norm)


originalBishopLogOnePlusCanonicalLimitUniqueOnUnitDisk :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (norm : BishopReal._≃_
    (Norm.normSqC w)
    (Norm.square ratio)) →
  (other : Complex.BishopComplex) →
  Complex.ComplexSeriesConvergesTo
    (Log.originalBishopLogOnePlusTerm w)
    other →
  Complex._≈C_
    (originalBishopLogOnePlusCanonicalLimitOnUnitDisk interval norm)
    other
originalBishopLogOnePlusCanonicalLimitUniqueOnUnitDisk {w} interval norm other convergence =
  Log.originalBishopLogOnePlusSeriesLimitUnique
    w
    (originalBishopLogOnePlusAbsoluteConvergenceOnUnitDisk interval norm)
    other
    convergence
