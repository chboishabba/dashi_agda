{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119PhysicalFiniteMeasureNZDNDZExact where

open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _-_)
open import Relation.Binary.PropositionalEquality using (refl)

import DASHI.Physics.Foundations.CMP119LiteralFiniteMeasureStressSourceConstructorExact as FiniteSource
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- ACTUAL FINITE-MEASURE N,Z,DN,DZ ALGEBRA
--
-- On the literal rational physical finite measure:
--
--   N  = ∫ rho O
--   Z  = partitionFunction
--   DN = ∫ ((D rho) O + rho (D O))
--   DZ = ∫ D rho
--
-- The base insertion O is independent of the chosen metric perturbation.
-- Only D rho and D O are perturbation-indexed.
------------------------------------------------------------------------

record PhysicalRationalMetricStressData
    (Configuration MetricPerturbation : Set)
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ) : Set₁ where
  field
    insertionObservable : Configuration → ℚ

    densityDerivative :
      MetricPerturbation → Configuration → ℚ

    insertionDerivative :
      MetricPerturbation → Configuration → ℚ

open PhysicalRationalMetricStressData public

weightedInsertionIntegrand :
  ∀ {Configuration MetricPerturbation}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ} →
  PhysicalRationalMetricStressData Configuration MetricPerturbation measure →
  Configuration → ℚ
weightedInsertionIntegrand {measure = measure} dataSet configuration =
  Physical.multiply measure
    (Physical.density measure configuration)
    (insertionObservable dataSet configuration)

numerator :
  ∀ {Configuration MetricPerturbation}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ} →
  PhysicalRationalMetricStressData Configuration MetricPerturbation measure →
  ℚ
numerator {measure = measure} dataSet =
  Physical.haarIntegral measure (weightedInsertionIntegrand dataSet)

denominator :
  ∀ {Configuration} →
  Physical.PhysicalFiniteYMMeasure Configuration ℚ → ℚ
denominator = Physical.partitionFunction

numeratorDerivativeIntegrand :
  ∀ {Configuration MetricPerturbation}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ} →
  PhysicalRationalMetricStressData Configuration MetricPerturbation measure →
  MetricPerturbation →
  Configuration → ℚ
numeratorDerivativeIntegrand {measure = measure} dataSet perturbation configuration =
  densityDerivative dataSet perturbation configuration
    * insertionObservable dataSet configuration
  +
  Physical.density measure configuration
    * insertionDerivative dataSet perturbation configuration

numeratorDerivative :
  ∀ {Configuration MetricPerturbation}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ} →
  PhysicalRationalMetricStressData Configuration MetricPerturbation measure →
  MetricPerturbation →
  ℚ
numeratorDerivative {measure = measure} dataSet perturbation =
  Physical.haarIntegral measure
    (numeratorDerivativeIntegrand dataSet perturbation)

denominatorDerivative :
  ∀ {Configuration MetricPerturbation}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ} →
  PhysicalRationalMetricStressData Configuration MetricPerturbation measure →
  MetricPerturbation →
  ℚ
denominatorDerivative {measure = measure} dataSet perturbation =
  Physical.haarIntegral measure
    (densityDerivative dataSet perturbation)

connectedCrossNumerator :
  ∀ {Configuration MetricPerturbation}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ} →
  PhysicalRationalMetricStressData Configuration MetricPerturbation measure →
  MetricPerturbation →
  ℚ
connectedCrossNumerator {measure = measure} dataSet perturbation =
  numeratorDerivative dataSet perturbation * denominator measure
    - numerator dataSet * denominatorDerivative dataSet perturbation

------------------------------------------------------------------------
-- Physical literal-carrier specialization.
------------------------------------------------------------------------

module _
    {G X Cutoff Configuration Observable Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     HilbertSpace Hamiltonian VacuumState : Set}
    where

  C : Top.LiteralYangMillsCarriers
  C =
    Physical.physicalLiteralCarriers
      G X Cutoff Configuration ℚ Observable Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      HilbertSpace Hamiltonian VacuumState

  record PhysicalRationalFiniteMeasureStressCalculus
      (MetricPerturbation : Set) : Set₁ where
    field
      stressDataAt :
        (measure : Top.FiniteMeasure C) →
        PhysicalRationalMetricStressData
          Configuration MetricPerturbation measure

  open PhysicalRationalFiniteMeasureStressCalculus public

  asLiteralFiniteMeasureNormalizedStressCalculus :
    ∀ {trajectory split inputs S Y group measureWeld MetricPerturbation} →
    PhysicalRationalFiniteMeasureStressCalculus MetricPerturbation →
    FiniteSource.LiteralFiniteMeasureNormalizedStressCalculus
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      measureWeld
  asLiteralFiniteMeasureNormalizedStressCalculus
      {MetricPerturbation = MetricPerturbation} calculus = record
    { FiniteSource.LiteralFiniteMeasureNormalizedStressCalculus.MetricPerturbation =
        MetricPerturbation
    ; FiniteSource.LiteralFiniteMeasureNormalizedStressCalculus.numerator =
        λ measure →
          numerator (stressDataAt calculus measure)
    ; FiniteSource.LiteralFiniteMeasureNormalizedStressCalculus.denominator =
        denominator
    ; FiniteSource.LiteralFiniteMeasureNormalizedStressCalculus.numeratorDerivative =
        λ measure perturbation →
          numeratorDerivative (stressDataAt calculus measure) perturbation
    ; FiniteSource.LiteralFiniteMeasureNormalizedStressCalculus.denominatorDerivative =
        λ measure perturbation →
          denominatorDerivative (stressDataAt calculus measure) perturbation
    ; FiniteSource.LiteralFiniteMeasureNormalizedStressCalculus.connectedInsertionNumerator =
        λ measure perturbation →
          connectedCrossNumerator (stressDataAt calculus measure) perturbation
    ; FiniteSource.LiteralFiniteMeasureNormalizedStressCalculus.normalizedCrossNumeratorIsConnectedInsertion =
        λ measure perturbation → refl
    }
