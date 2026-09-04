module DASHI.Analysis.BishopTrigonometricDerivedSeriesConvergenceExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopConcreteSeriesConvergenceTransportExact as Transport

------------------------------------------------------------------------
-- BISHOP TRIGONOMETRIC DERIVED-SERIES CONVERGENCE
--
-- master already owns convergence of the literal sine/cosine series and
-- transport of convergence across pointwise-equivalent term families.
-- Therefore, once finite coefficient differentiation identifies a derived sine
-- term with the cosine term (and a derived cosine term with minus sine), the
-- corresponding derived-series limits are compiler output.
--
-- This file does not assert that differentiation commutes with the infinite
-- series.  That remains a distinct calculus/interchange receipt.
------------------------------------------------------------------------

record TrigonometricDerivedTermIdentification
    (dataSet : Elementary.BishopElementaryPowerSeriesData) : Set₁ where
  field
    sineDerivedTerm cosineDerivedTerm :
      BishopReal.ℝ → Nat → BishopReal.ℝ

    sineDerivedTermIsCosineTerm : ∀ point index →
      BishopReal._≃_
        (sineDerivedTerm point index)
        (Elementary.cosineTerm dataSet point index)

    cosineDerivedTermIsNegativeSineTerm : ∀ point index →
      BishopReal._≃_
        (cosineDerivedTerm point index)
        (BishopReal.- (Elementary.sineTerm dataSet point index))

open TrigonometricDerivedTermIdentification public

sineDerivedSeriesConvergesToCosine :
  ∀ {dataSet : Elementary.BishopElementaryPowerSeriesData} →
  (D : TrigonometricDerivedTermIdentification dataSet) →
  (point : BishopReal.ℝ) →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf (sineDerivedTerm D point))
    (Elementary.bishopCos dataSet point)
sineDerivedSeriesConvergesToCosine {dataSet} D point =
  Transport.pointwiseEquivalentSeriesConvergenceFromRight
    (sineDerivedTermIsCosineTerm D point)
    (Elementary.bishopCosConvergence dataSet point)

cosineDerivedSeriesConvergesToNegativeSine :
  ∀ {dataSet : Elementary.BishopElementaryPowerSeriesData} →
  (D : TrigonometricDerivedTermIdentification dataSet) →
  (point : BishopReal.ℝ) →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf (cosineDerivedTerm D point))
    (BishopReal.- (Elementary.bishopSin dataSet point))
cosineDerivedSeriesConvergesToNegativeSine {dataSet} D point =
  Transport.pointwiseEquivalentSeriesConvergenceFromRight
    (cosineDerivedTermIsNegativeSineTerm D point)
    (Transport.seriesNegationConvergence
      (Elementary.bishopSinConvergence dataSet point))

record ReverseTrigDerivativeObligations : Set where
  field
    finiteSineTermDerivativeIdentity : Set
    finiteCosineTermDerivativeIdentity : Set
    derivativeSeriesInterchange : Set
    sameBishopSineCosineObject : Set

open ReverseTrigDerivativeObligations public

data DerivedSeriesLimitAutomaticallyIsFunctionDerivative : Set where

derivedSeriesLimitDoesNotAutoProveInterchange :
  DerivedSeriesLimitAutomaticallyIsFunctionDerivative → ⊥
derivedSeriesLimitDoesNotAutoProveInterchange ()
