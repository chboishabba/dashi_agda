module DASHI.Moonshine.AbelBishopKoenigsGeometricAbsoluteExact where

------------------------------------------------------------------------
-- DIRECT VENDORED BISHOP COMPARISON FOR SCHROEDER/KOENIGS INCREMENTS
--
-- This module DOES NOT assume convergence of the original increments.
-- It derives it from source-order domination by an existing, genuinely
-- Bishop-convergent scaled geometric series.
--
-- Unpaid producer: original principal Log remainder -> componentwise bounds.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Product.Base using (_,_)

import Real as Bishop
import RealProperties as BishopP
import Sequence as Sequence

import DASHI.Foundations.BishopPolynomialGeometricDominationConvergenceExact as Geom
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Moonshine.AbelBishopKoenigsIncrementSeriesExact as Increment
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion

record OriginalBishopGeometricComponentBounds
    (terms : Nat → Complex.BishopComplex)
    (constant ratio : Bishop.ℝ) : Set₁ where
  field
    geometricInputs :
      Geom.BishopScaledGeometricInputs constant ratio

    realComponentBound :
      ∀ n →
      Bishop._≤_
        (Bishop.∣ Complex.re (terms n) ∣)
        (Geom.scaledGeometricTerm constant ratio n)

    imaginaryComponentBound :
      ∀ n →
      Bishop._≤_
        (Bishop.∣ Complex.im (terms n) ∣)
        (Geom.scaledGeometricTerm constant ratio n)

open OriginalBishopGeometricComponentBounds public

originalBishopGeometricAbsoluteFromBound :
  (terms : Nat → Bishop.ℝ) →
  (constant ratio : Bishop.ℝ) →
  (inputs : Geom.BishopScaledGeometricInputs constant ratio) →
  (∀ n →
    Bishop._≤_
      (Bishop.∣ terms n ∣)
      (Geom.scaledGeometricTerm constant ratio n)) →
  Sequence.SeriesOf_ConvergesAbsolutely terms
originalBishopGeometricAbsoluteFromBound terms constant ratio inputs bound =
  Sequence.proposition-3-5
    (Geom.scaledGeometricSeriesConvergent inputs)
    (zero , λ n _ →
      BishopP.≤-respˡ-≃
        (BishopP.nonNegx⇒∣x∣≃x
          (BishopP.nonNeg∣x∣ (terms n)))
        (bound n))

originalBishopKoenigsComponentAbsoluteSummability :
  (terms : Nat → Complex.BishopComplex) →
  (constant ratio : Bishop.ℝ) →
  OriginalBishopGeometricComponentBounds terms constant ratio →
  Complex.ComponentwiseAbsoluteSeriesConvergent terms
originalBishopKoenigsComponentAbsoluteSummability terms constant ratio inputs =
  Complex.componentwise-absolute-series-convergent
    (originalBishopGeometricAbsoluteFromBound
      (Complex.realTerms terms)
      constant ratio
      (geometricInputs inputs)
      (realComponentBound inputs))
    (originalBishopGeometricAbsoluteFromBound
      (Complex.imagTerms terms)
      constant ratio
      (geometricInputs inputs)
      (imaginaryComponentBound inputs))

originalBishopKoenigsGeometricCauchy :
  (terms : Nat → Complex.BishopComplex) →
  (constant ratio : Bishop.ℝ) →
  (bounds : OriginalBishopGeometricComponentBounds terms constant ratio) →
  Completion.OriginalBishopComplexCauchy
    (Increment.originalBishopKoenigsIncrementPrefix terms)
originalBishopKoenigsGeometricCauchy terms constant ratio bounds =
  Increment.originalBishopKoenigsFiniteTailToCauchy terms
    (originalBishopKoenigsComponentAbsoluteSummability terms constant ratio bounds)

originalBishopKoenigsGeometricLimit :
  (terms : Nat → Complex.BishopComplex) →
  (constant ratio : Bishop.ℝ) →
  (bounds : OriginalBishopGeometricComponentBounds terms constant ratio) →
  Complex.BishopComplex
originalBishopKoenigsGeometricLimit terms constant ratio bounds =
  Increment.originalBishopKoenigsIncrementLimit terms
    (originalBishopKoenigsComponentAbsoluteSummability
      terms constant ratio bounds)

originalBishopKoenigsGeometricLimitConverges :
  (terms : Nat → Complex.BishopComplex) →
  (constant ratio : Bishop.ℝ) →
  (bounds : OriginalBishopGeometricComponentBounds terms constant ratio) →
  Completion.OriginalBishopPointwiseComplexConverges
    (Increment.originalBishopKoenigsIncrementPrefix terms)
    (originalBishopKoenigsGeometricLimit terms constant ratio bounds)
originalBishopKoenigsGeometricLimitConverges terms constant ratio bounds =
  Increment.originalBishopKoenigsIncrementLimitConverges terms
    (originalBishopKoenigsComponentAbsoluteSummability
      terms constant ratio bounds)
