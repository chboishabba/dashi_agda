{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRealHaarStrictPositivityExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _≤ℝ_; _<ℝ_)
import DASHI.Physics.Foundations.CMP119AntigravityRealStrictSignExact as Strict
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite

------------------------------------------------------------------------
-- STRICT POSITIVITY ON THE LITERAL REAL CMP119 HAAR FUNCTIONAL
--
-- The finite lattice still has continuous compact-group configuration space.
-- Strict positivity is therefore expressed by a positive-integral minorant on
-- the actual real Haar functional, not by an exact finite quadrature.
------------------------------------------------------------------------

record OrderedRealHaarIntegrationLaws
    {Configuration : Set}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ) : Set₁ where
  field
    base :
      Finite.PhysicalFiniteMeasureIntegrationLaws measure

    haarIntegralMonotone :
      ∀ left right →
      (∀ configuration → left configuration ≤ℝ right configuration) →
      Physical.haarIntegral measure left
      ≤ℝ Physical.haarIntegral measure right

open OrderedRealHaarIntegrationLaws public

record StrictPositiveRealHaarMinorant
    {Configuration : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ}
    (ordered : OrderedRealHaarIntegrationLaws measure)
    (integrand : Configuration → ℝ) : Set₁ where
  field
    minorant : Configuration → ℝ

    minorantBelow :
      ∀ configuration →
      minorant configuration ≤ℝ integrand configuration

    minorantIntegralPositive :
      0ℝ <ℝ Physical.haarIntegral measure minorant

open StrictPositiveRealHaarMinorant public

haarIntegralStrictlyPositiveFromMinorant :
  ∀ {Configuration measure}
    (strict : Strict.RealStrictSignLaws)
    {ordered : OrderedRealHaarIntegrationLaws
      {Configuration = Configuration} measure}
    {integrand : Configuration → ℝ} →
  StrictPositiveRealHaarMinorant ordered integrand →
  0ℝ <ℝ Physical.haarIntegral measure integrand
haarIntegralStrictlyPositiveFromMinorant strict {measure = measure}
    {ordered = ordered} {integrand = integrand} witness =
  Strict.strictThenWeak strict
    (minorantIntegralPositive witness)
    (haarIntegralMonotone ordered
      (minorant witness) integrand
      (minorantBelow witness))

record PositiveRealPartitionWitness
    {Configuration : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ}
    (ordered : OrderedRealHaarIntegrationLaws measure) : Set₁ where
  field
    densityMinorant :
      StrictPositiveRealHaarMinorant ordered
        (Physical.density measure)

open PositiveRealPartitionWitness public

partitionFunctionPositive :
  ∀ {Configuration measure}
    (strict : Strict.RealStrictSignLaws)
    (ordered : OrderedRealHaarIntegrationLaws
      {Configuration = Configuration} measure) →
  PositiveRealPartitionWitness ordered →
  0ℝ <ℝ Physical.partitionFunction measure
partitionFunctionPositive {measure = measure} strict ordered witness =
  subst
    (λ value → 0ℝ <ℝ value)
    (sym
      (Finite.partitionFunctionIsDensityIntegral
        (base ordered)))
    (haarIntegralStrictlyPositiveFromMinorant
      strict (densityMinorant witness))

weightedObservable :
  ∀ {Configuration}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ} →
  (Configuration → ℝ) →
  Configuration → ℝ
weightedObservable {measure = measure} observable configuration =
  Physical.density measure configuration
  *ℝ observable configuration

weightedNumerator :
  ∀ {Configuration}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ} →
  (Configuration → ℝ) →
  ℝ
weightedNumerator {measure = measure} observable =
  Physical.haarIntegral measure
    (weightedObservable observable)

record PositiveWeightedRealHaarWitness
    {Configuration : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ}
    (ordered : OrderedRealHaarIntegrationLaws measure)
    (observable : Configuration → ℝ) : Set₁ where
  field
    weightedMinorant :
      StrictPositiveRealHaarMinorant ordered
        (weightedObservable observable)

open PositiveWeightedRealHaarWitness public

weightedNumeratorPositive :
  ∀ {Configuration measure}
    (strict : Strict.RealStrictSignLaws)
    (ordered : OrderedRealHaarIntegrationLaws
      {Configuration = Configuration} measure)
    (observable : Configuration → ℝ) →
  PositiveWeightedRealHaarWitness ordered observable →
  0ℝ <ℝ weightedNumerator {measure = measure} observable
weightedNumeratorPositive strict ordered observable witness =
  haarIntegralStrictlyPositiveFromMinorant
    strict (weightedMinorant witness)
