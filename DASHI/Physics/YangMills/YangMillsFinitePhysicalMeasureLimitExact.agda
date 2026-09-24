{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact where

------------------------------------------------------------------------
-- LITERAL A CONSTRUCTION:
-- LIMIT OF ALREADY-NORMALIZED FINITE PHYSICAL EXPECTATIONS
--
-- Define
--
--   E∞(O) = lim_n E_n(O)
--
-- directly.  This avoids an unnecessary continuum partition-function ratio.
-- Finite nonzero partition functions are still needed to define each E_n, but
-- no limiting denominator or division-continuity theorem is required.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division
import DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact as Cylinder
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite

record FinitePhysicalNormalizedFamily
    (Configuration : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient) : Set₁ where
  field
    finiteMeasure :
      Nat → Physical.PhysicalFiniteYMMeasure Configuration ℝ

    integrationLaws :
      ∀ cutoff →
      Finite.PhysicalFiniteMeasureIntegrationLaws
        (finiteMeasure cutoff)

    partitionNonzero :
      ∀ cutoff →
      Quotient.Nonzero quotient
        (Physical.partitionFunction (finiteMeasure cutoff))

open FinitePhysicalNormalizedFamily public

finiteExpectation :
  ∀ {Configuration sequenceLimit limitLaws quotient division} →
  FinitePhysicalNormalizedFamily
    Configuration limitLaws quotient division →
  Nat → (Configuration → ℝ) → ℝ
finiteExpectation {quotient = quotient} family cutoff observable =
  Quotient.divide quotient
    (Finite.unnormalizedNumerator
      (finiteMeasure family cutoff) observable)
    (Physical.partitionFunction
      (finiteMeasure family cutoff))

finiteExpectationZero :
  ∀ {Configuration sequenceLimit limitLaws quotient division}
    (family :
      FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division)
    cutoff →
  finiteExpectation family cutoff Finite.zeroObservable ≡ 0ℝ
finiteExpectationZero
    {quotient = quotient} {division = division}
    family cutoff =
  subst
    (λ numerator →
      Quotient.divide quotient numerator
        (Physical.partitionFunction
          (finiteMeasure family cutoff))
      ≡ 0ℝ)
    (Finite.numeratorZero (integrationLaws family cutoff))
    (Division.divideZero division
      (Physical.partitionFunction
        (finiteMeasure family cutoff))
      (partitionNonzero family cutoff))

finiteExpectationOne :
  ∀ {Configuration sequenceLimit limitLaws quotient division}
    (family :
      FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division)
    cutoff →
  finiteExpectation family cutoff Finite.oneObservable ≡ 1ℝ
finiteExpectationOne
    {quotient = quotient} {division = division}
    family cutoff =
  subst
    (λ numerator →
      Quotient.divide quotient numerator
        (Physical.partitionFunction
          (finiteMeasure family cutoff))
      ≡ 1ℝ)
    (Finite.numeratorOneIsPartitionFunction
      (integrationLaws family cutoff))
    (Division.divideSelf division
      (Physical.partitionFunction
        (finiteMeasure family cutoff))
      (partitionNonzero family cutoff))

finiteExpectationAdd :
  ∀ {Configuration sequenceLimit limitLaws quotient division}
    (family :
      FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division)
    cutoff left right →
  finiteExpectation family cutoff
    (Finite.addObservable left right)
  ≡
  finiteExpectation family cutoff left
    +ℝ finiteExpectation family cutoff right
finiteExpectationAdd
    {quotient = quotient} {division = division}
    family cutoff left right =
  subst
    (λ numerator →
      Quotient.divide quotient numerator
        (Physical.partitionFunction
          (finiteMeasure family cutoff))
      ≡
      finiteExpectation family cutoff left
        +ℝ finiteExpectation family cutoff right)
    (Finite.numeratorAdd
      (integrationLaws family cutoff) left right)
    (Division.divideAddNumerator division
      (Finite.unnormalizedNumerator
        (finiteMeasure family cutoff) left)
      (Finite.unnormalizedNumerator
        (finiteMeasure family cutoff) right)
      (Physical.partitionFunction
        (finiteMeasure family cutoff))
      (partitionNonzero family cutoff))

finiteExpectationScale :
  ∀ {Configuration sequenceLimit limitLaws quotient division}
    (family :
      FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division)
    cutoff scalar observable →
  finiteExpectation family cutoff
    (Finite.scaleObservable scalar observable)
  ≡
  scalar *ℝ finiteExpectation family cutoff observable
finiteExpectationScale
    {quotient = quotient} {division = division}
    family cutoff scalar observable =
  subst
    (λ numerator →
      Quotient.divide quotient numerator
        (Physical.partitionFunction
          (finiteMeasure family cutoff))
      ≡
      scalar *ℝ finiteExpectation family cutoff observable)
    (Finite.numeratorScale
      (integrationLaws family cutoff) scalar observable)
    (Division.divideScaleNumerator division
      scalar
      (Finite.unnormalizedNumerator
        (finiteMeasure family cutoff) observable)
      (Physical.partitionFunction
        (finiteMeasure family cutoff))
      (partitionNonzero family cutoff))

finiteExpectationPositive :
  ∀ {Configuration sequenceLimit limitLaws quotient division}
    (family :
      FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division)
    cutoff observable →
  Finite.PointwiseNonnegative observable →
  0ℝ ≤ℝ finiteExpectation family cutoff observable
finiteExpectationPositive
    {division = division} family cutoff observable nonnegative =
  Division.dividePreservesNonnegative division
    (Finite.unnormalizedNumerator
      (finiteMeasure family cutoff) observable)
    (Physical.partitionFunction
      (finiteMeasure family cutoff))
    (Finite.numeratorPositive
      (integrationLaws family cutoff)
      observable nonnegative)
    (partitionNonzero family cutoff)

limitExpectation :
  ∀ {Configuration sequenceLimit limitLaws quotient division} →
  FinitePhysicalNormalizedFamily
    Configuration limitLaws quotient division →
  (Configuration → ℝ) → ℝ
limitExpectation
    {sequenceLimit = sequenceLimit} family observable =
  Seq.limit sequenceLimit
    (λ cutoff → finiteExpectation family cutoff observable)

asCylinderLimitData :
  ∀ {Configuration sequenceLimit limitLaws quotient division}
    (family :
      FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division) →
  Cylinder.ScalarCylinderExpectationLimitData
    (Configuration → ℝ) ℝ
    (RealLimit.canonicalCylinderAlgebra limitLaws)
asCylinderLimitData
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} family = record
  { Cylinder.ScalarCylinderExpectationLimitData.zeroObservable =
      Finite.zeroObservable
  ; Cylinder.ScalarCylinderExpectationLimitData.oneObservable =
      Finite.oneObservable
  ; Cylinder.ScalarCylinderExpectationLimitData.addObservable =
      Finite.addObservable
  ; Cylinder.ScalarCylinderExpectationLimitData.scaleObservable =
      Finite.scaleObservable
  ; Cylinder.ScalarCylinderExpectationLimitData.Nonnegative =
      Finite.PointwiseNonnegative
  ; Cylinder.ScalarCylinderExpectationLimitData.finiteExpectation =
      finiteExpectation family
  ; Cylinder.ScalarCylinderExpectationLimitData.limitExpectation =
      limitExpectation family
  ; Cylinder.ScalarCylinderExpectationLimitData.finiteZero =
      finiteExpectationZero family
  ; Cylinder.ScalarCylinderExpectationLimitData.finiteOne =
      finiteExpectationOne family
  ; Cylinder.ScalarCylinderExpectationLimitData.finiteAdd =
      finiteExpectationAdd family
  ; Cylinder.ScalarCylinderExpectationLimitData.finiteScale =
      finiteExpectationScale family
  ; Cylinder.ScalarCylinderExpectationLimitData.finitePositive =
      finiteExpectationPositive family
  ; Cylinder.ScalarCylinderExpectationLimitData.selectedConverges =
      λ observable → refl
  }

continuumMeasure :
  ∀ {Configuration sequenceLimit limitLaws quotient division} →
  FinitePhysicalNormalizedFamily
    Configuration limitLaws quotient division →
  Physical.PhysicalContinuumYMMeasure (Configuration → ℝ) ℝ
continuumMeasure family =
  Physical.physicalContinuumMeasure
    (limitExpectation family)

continuumMeasureNormalized :
  ∀ {Configuration sequenceLimit limitLaws quotient division}
    (family :
      FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division) →
  Physical.expectation
    (continuumMeasure family)
    Finite.oneObservable
  ≡ 1ℝ
continuumMeasureNormalized family =
  Cylinder.limitOne (asCylinderLimitData family)

continuumMeasurePositive :
  ∀ {Configuration sequenceLimit limitLaws quotient division}
    (family :
      FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division)
    observable →
  Finite.PointwiseNonnegative observable →
  0ℝ ≤ℝ
    Physical.expectation
      (continuumMeasure family)
      observable
continuumMeasurePositive family observable nonnegative =
  Cylinder.limitPositive
    (asCylinderLimitData family)
    observable nonnegative

finitePhysicalExpectationLimitCompilerLevel : ProofLevel
finitePhysicalExpectationLimitCompilerLevel = machineChecked

continuumPhysicalMeasureNormalizationCompilerLevel : ProofLevel
continuumPhysicalMeasureNormalizationCompilerLevel = machineChecked

continuumPhysicalMeasurePositivityCompilerLevel : ProofLevel
continuumPhysicalMeasurePositivityCompilerLevel = machineChecked

-- Only finite-stage physical inputs remain for this construction:
-- literal Haar integration laws and nonzero partition function at each cutoff.
literalFiniteHaarIntegrationAndPartitionInputsLevel : ProofLevel
literalFiniteHaarIntegrationAndPartitionInputsLevel = conditional
