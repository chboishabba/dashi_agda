{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119GibbsConnectedNumeratorEvaluationExact where

open import Data.Rational.Base as ℚ using (ℚ; _*_; _-_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119PhysicalFiniteMeasureNZDNDZExact as NZ
import DASHI.Physics.Foundations.CMP119GibbsFiniteMeasureNZDNDZReductionExact as Gibbs
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- TERMINAL FINITE-MEASURE EVALUATION FORMULA
--
-- For one selected metric perturbation h:
--
--   A   = ∫ rho O
--   B_h = ∫ [(-rho DS_h) O + rho DO_h]
--   D_h = ∫ (-rho DS_h)
--   Z   = partitionFunction
--
-- and the division-free connected numerator is
--
--   C_h = B_h Z - A D_h.
------------------------------------------------------------------------

module _
    {Configuration MetricPerturbation : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
    (dataSet : Gibbs.GibbsMetricInsertionData
      Configuration MetricPerturbation measure)
  where

  A : ℚ
  A =
    NZ.numerator (Gibbs.asPhysicalMetricStressData dataSet)

  Z : ℚ
  Z = NZ.denominator measure

  B : MetricPerturbation → ℚ
  B perturbation =
    NZ.numeratorDerivative
      (Gibbs.asPhysicalMetricStressData dataSet)
      perturbation

  D : MetricPerturbation → ℚ
  D perturbation =
    NZ.denominatorDerivative
      (Gibbs.asPhysicalMetricStressData dataSet)
      perturbation

  C : MetricPerturbation → ℚ
  C perturbation =
    B perturbation * Z - A * D perturbation

  connectedCrossNumeratorIsABDZ :
    ∀ perturbation →
    NZ.connectedCrossNumerator
      (Gibbs.asPhysicalMetricStressData dataSet)
      perturbation
    ≡ C perturbation
  connectedCrossNumeratorIsABDZ perturbation = refl

  AIsHaarInsertionIntegral :
    A
    ≡
    Physical.haarIntegral measure
      (λ configuration →
        Physical.density measure configuration
        * Gibbs.insertionObservable dataSet configuration)
  AIsHaarInsertionIntegral =
    Gibbs.numeratorIsLiteralHaarInsertionIntegral dataSet

  BIsHaarMetricInsertionDerivative :
    ∀ perturbation →
    B perturbation
    ≡
    Physical.haarIntegral measure
      (Gibbs.gibbsNumeratorDerivativeIntegrand dataSet perturbation)
  BIsHaarMetricInsertionDerivative =
    Gibbs.numeratorDerivativeIsLiteralHaarMetricVariation dataSet

  DIsHaarDensityDerivative :
    ∀ perturbation →
    D perturbation
    ≡
    Physical.haarIntegral measure
      (Gibbs.gibbsDenominatorDerivativeIntegrand dataSet perturbation)
  DIsHaarDensityDerivative =
    Gibbs.denominatorDerivativeIsLiteralHaarMetricVariation dataSet

  ZIsPartitionFunction :
    Z ≡ Physical.partitionFunction measure
  ZIsPartitionFunction =
    Gibbs.denominatorIsLiteralPartitionFunction dataSet
