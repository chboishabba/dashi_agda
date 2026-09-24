{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119GibbsFiniteMeasureNZDNDZReductionExact where

open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; -_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119PhysicalFiniteMeasureNZDNDZExact as NZ
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- GIBBS REDUCTION OF THE FINITE-MEASURE METRIC DERIVATIVE
--
-- For rho = exp(-S) (or any Gibbs weight with the same logarithmic derivative),
--
--   D rho[h] = - rho DS[h].
--
-- Hence the selected normalized insertion needs only:
--   O        base insertion observable,
--   DS[h]    metric variation of the finite action,
--   DO[h]    metric variation of the insertion.
------------------------------------------------------------------------

record GibbsMetricInsertionData
    (Configuration MetricPerturbation : Set)
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ) : Set₁ where
  field
    insertionObservable : Configuration → ℚ

    actionVariation :
      MetricPerturbation → Configuration → ℚ

    insertionVariation :
      MetricPerturbation → Configuration → ℚ

open GibbsMetricInsertionData public

gibbsDensityDerivative :
  ∀ {Configuration MetricPerturbation}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ} →
  GibbsMetricInsertionData Configuration MetricPerturbation measure →
  MetricPerturbation → Configuration → ℚ
gibbsDensityDerivative {measure = measure} dataSet perturbation configuration =
  - (Physical.density measure configuration
      * actionVariation dataSet perturbation configuration)

asPhysicalMetricStressData :
  ∀ {Configuration MetricPerturbation}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ} →
  GibbsMetricInsertionData Configuration MetricPerturbation measure →
  NZ.PhysicalRationalMetricStressData
    Configuration MetricPerturbation measure
asPhysicalMetricStressData dataSet = record
  { NZ.PhysicalRationalMetricStressData.insertionObservable =
      insertionObservable dataSet
  ; NZ.PhysicalRationalMetricStressData.densityDerivative =
      gibbsDensityDerivative dataSet
  ; NZ.PhysicalRationalMetricStressData.insertionDerivative =
      insertionVariation dataSet
  }

gibbsNumeratorDerivativeIntegrand :
  ∀ {Configuration MetricPerturbation}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ} →
  GibbsMetricInsertionData Configuration MetricPerturbation measure →
  MetricPerturbation → Configuration → ℚ
gibbsNumeratorDerivativeIntegrand {measure = measure}
    dataSet perturbation configuration =
  Physical.density measure configuration
    * insertionVariation dataSet perturbation configuration
  +
  (- (Physical.density measure configuration
        * actionVariation dataSet perturbation configuration))
    * insertionObservable dataSet configuration

gibbsDenominatorDerivativeIntegrand :
  ∀ {Configuration MetricPerturbation}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ} →
  GibbsMetricInsertionData Configuration MetricPerturbation measure →
  MetricPerturbation → Configuration → ℚ
gibbsDenominatorDerivativeIntegrand =
  gibbsDensityDerivative

numeratorIsLiteralHaarInsertionIntegral :
  ∀ {Configuration MetricPerturbation}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
    (dataSet : GibbsMetricInsertionData Configuration MetricPerturbation measure) →
  NZ.numerator (asPhysicalMetricStressData dataSet)
  ≡
  Physical.haarIntegral measure
    (λ configuration →
      Physical.density measure configuration
        * insertionObservable dataSet configuration)
numeratorIsLiteralHaarInsertionIntegral dataSet = refl

denominatorIsLiteralPartitionFunction :
  ∀ {Configuration MetricPerturbation}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
    (dataSet : GibbsMetricInsertionData Configuration MetricPerturbation measure) →
  NZ.denominator measure ≡ Physical.partitionFunction measure
denominatorIsLiteralPartitionFunction dataSet = refl

numeratorDerivativeIsLiteralHaarMetricVariation :
  ∀ {Configuration MetricPerturbation}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
    (dataSet : GibbsMetricInsertionData Configuration MetricPerturbation measure)
    perturbation →
  NZ.numeratorDerivative (asPhysicalMetricStressData dataSet) perturbation
  ≡
  Physical.haarIntegral measure
    (gibbsNumeratorDerivativeIntegrand dataSet perturbation)
numeratorDerivativeIsLiteralHaarMetricVariation dataSet perturbation = refl

denominatorDerivativeIsLiteralHaarMetricVariation :
  ∀ {Configuration MetricPerturbation}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
    (dataSet : GibbsMetricInsertionData Configuration MetricPerturbation measure)
    perturbation →
  NZ.denominatorDerivative (asPhysicalMetricStressData dataSet) perturbation
  ≡
  Physical.haarIntegral measure
    (gibbsDenominatorDerivativeIntegrand dataSet perturbation)
denominatorDerivativeIsLiteralHaarMetricVariation dataSet perturbation = refl
