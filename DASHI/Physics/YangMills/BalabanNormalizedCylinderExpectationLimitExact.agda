{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact where

------------------------------------------------------------------------
-- UNNORMALIZED CMP119/HAAR LIMITS -> NORMALIZED CYLINDER LIMIT
--
-- One real convergence algebra is shared throughout.
-- Physics supplies convergence of the unnormalized observable numerators and
-- partition function.  Standard real-field quotient laws then construct the
-- normalized cylinder expectation data consumed by literal A.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact as Cylinder

record RealDivisionAlgebra
    (algebra : Cylinder.ScalarCylinderLimitAlgebra ℝ)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (Cylinder.Converges algebra)) : Set₁ where
  field
    divideZero :
      ∀ denominator →
      Quotient.Nonzero quotient denominator →
      Quotient.divide quotient 0ℝ denominator ≡ 0ℝ

    divideSelf :
      ∀ denominator →
      Quotient.Nonzero quotient denominator →
      Quotient.divide quotient denominator denominator ≡ 1ℝ

    divideAddNumerator :
      ∀ left right denominator →
      Quotient.Nonzero quotient denominator →
      Quotient.divide quotient (left +ℝ right) denominator
      ≡
      Quotient.divide quotient left denominator
        +ℝ Quotient.divide quotient right denominator

    divideScaleNumerator :
      ∀ scalar numerator denominator →
      Quotient.Nonzero quotient denominator →
      Quotient.divide quotient (scalar *ℝ numerator) denominator
      ≡
      scalar *ℝ Quotient.divide quotient numerator denominator

    dividePreservesNonnegative :
      ∀ numerator denominator →
      0ℝ ≤ℝ numerator →
      Quotient.Nonzero quotient denominator →
      0ℝ ≤ℝ Quotient.divide quotient numerator denominator

open RealDivisionAlgebra public

record NormalizedCylinderSourceData
    (Observable : Set)
    (algebra : Cylinder.ScalarCylinderLimitAlgebra ℝ)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (Cylinder.Converges algebra))
    (division : RealDivisionAlgebra algebra quotient) : Set₁ where
  field
    zeroObservable oneObservable : Observable
    addObservable : Observable → Observable → Observable
    scaleObservable : ℝ → Observable → Observable
    Nonnegative : Observable → Set

    unnormalizedNumerator :
      Nat → Observable → ℝ

    partitionFunction :
      Nat → ℝ

    continuumNumerator :
      Observable → ℝ

    continuumPartitionFunction :
      ℝ

    numeratorConverges :
      ∀ observable →
      Cylinder.Converges algebra
        (λ n → unnormalizedNumerator n observable)
        (continuumNumerator observable)

    partitionConverges :
      Cylinder.Converges algebra
        partitionFunction continuumPartitionFunction

    finitePartitionNonzero :
      ∀ n → Quotient.Nonzero quotient (partitionFunction n)

    continuumPartitionNonzero :
      Quotient.Nonzero quotient continuumPartitionFunction

    numeratorZero :
      ∀ n → unnormalizedNumerator n zeroObservable ≡ 0ℝ

    numeratorOne :
      ∀ n → unnormalizedNumerator n oneObservable ≡ partitionFunction n

    numeratorAdd :
      ∀ n left right →
      unnormalizedNumerator n (addObservable left right)
      ≡
      unnormalizedNumerator n left
        +ℝ unnormalizedNumerator n right

    numeratorScale :
      ∀ n scalar observable →
      unnormalizedNumerator n (scaleObservable scalar observable)
      ≡
      scalar *ℝ unnormalizedNumerator n observable

    numeratorPositive :
      ∀ n observable →
      Nonnegative observable →
      0ℝ ≤ℝ unnormalizedNumerator n observable

open NormalizedCylinderSourceData public

finiteNormalized :
  ∀ {Observable algebra quotient division} →
  NormalizedCylinderSourceData
    Observable algebra quotient division →
  Nat → Observable → ℝ
finiteNormalized {quotient = quotient} dataSet n observable =
  Quotient.divide quotient
    (unnormalizedNumerator dataSet n observable)
    (partitionFunction dataSet n)

continuumNormalized :
  ∀ {Observable algebra quotient division} →
  NormalizedCylinderSourceData
    Observable algebra quotient division →
  Observable → ℝ
continuumNormalized {quotient = quotient} dataSet observable =
  Quotient.divide quotient
    (continuumNumerator dataSet observable)
    (continuumPartitionFunction dataSet)

normalizedConverges :
  ∀ {Observable algebra quotient division}
    (dataSet :
      NormalizedCylinderSourceData
        Observable algebra quotient division)
    observable →
  Cylinder.Converges algebra
    (λ n → finiteNormalized dataSet n observable)
    (continuumNormalized dataSet observable)
normalizedConverges
    {quotient = quotient} dataSet observable =
  Quotient.quotientConverges quotient
    (λ n → unnormalizedNumerator dataSet n observable)
    (partitionFunction dataSet)
    (continuumNumerator dataSet observable)
    (continuumPartitionFunction dataSet)
    (numeratorConverges dataSet observable)
    (partitionConverges dataSet)
    (continuumPartitionNonzero dataSet)

finiteNormalizedZero :
  ∀ {Observable algebra quotient division}
    (dataSet :
      NormalizedCylinderSourceData
        Observable algebra quotient division)
    n →
  finiteNormalized dataSet n (zeroObservable dataSet)
  ≡ 0ℝ
finiteNormalizedZero
    {quotient = quotient} {division = division}
    dataSet n =
  subst
    (λ numerator →
      Quotient.divide quotient numerator
        (partitionFunction dataSet n)
      ≡ 0ℝ)
    (numeratorZero dataSet n)
    (divideZero division
      (partitionFunction dataSet n)
      (finitePartitionNonzero dataSet n))

finiteNormalizedOne :
  ∀ {Observable algebra quotient division}
    (dataSet :
      NormalizedCylinderSourceData
        Observable algebra quotient division)
    n →
  finiteNormalized dataSet n (oneObservable dataSet)
  ≡ 1ℝ
finiteNormalizedOne
    {quotient = quotient} {division = division}
    dataSet n =
  subst
    (λ numerator →
      Quotient.divide quotient numerator
        (partitionFunction dataSet n)
      ≡ 1ℝ)
    (numeratorOne dataSet n)
    (divideSelf division
      (partitionFunction dataSet n)
      (finitePartitionNonzero dataSet n))

finiteNormalizedAdd :
  ∀ {Observable algebra quotient division}
    (dataSet :
      NormalizedCylinderSourceData
        Observable algebra quotient division)
    n left right →
  finiteNormalized dataSet n
    (addObservable dataSet left right)
  ≡
  finiteNormalized dataSet n left
    +ℝ finiteNormalized dataSet n right
finiteNormalizedAdd
    {quotient = quotient} {division = division}
    dataSet n left right =
  subst
    (λ numerator →
      Quotient.divide quotient numerator
        (partitionFunction dataSet n)
      ≡
      finiteNormalized dataSet n left
        +ℝ finiteNormalized dataSet n right)
    (numeratorAdd dataSet n left right)
    (divideAddNumerator division
      (unnormalizedNumerator dataSet n left)
      (unnormalizedNumerator dataSet n right)
      (partitionFunction dataSet n)
      (finitePartitionNonzero dataSet n))

finiteNormalizedScale :
  ∀ {Observable algebra quotient division}
    (dataSet :
      NormalizedCylinderSourceData
        Observable algebra quotient division)
    n scalar observable →
  finiteNormalized dataSet n
    (scaleObservable dataSet scalar observable)
  ≡
  scalar *ℝ finiteNormalized dataSet n observable
finiteNormalizedScale
    {quotient = quotient} {division = division}
    dataSet n scalar observable =
  subst
    (λ numerator →
      Quotient.divide quotient numerator
        (partitionFunction dataSet n)
      ≡ scalar *ℝ finiteNormalized dataSet n observable)
    (numeratorScale dataSet n scalar observable)
    (divideScaleNumerator division
      scalar
      (unnormalizedNumerator dataSet n observable)
      (partitionFunction dataSet n)
      (finitePartitionNonzero dataSet n))

finiteNormalizedPositive :
  ∀ {Observable algebra quotient division}
    (dataSet :
      NormalizedCylinderSourceData
        Observable algebra quotient division)
    n observable →
  Nonnegative dataSet observable →
  0ℝ ≤ℝ finiteNormalized dataSet n observable
finiteNormalizedPositive
    {division = division} dataSet n observable nonnegative =
  dividePreservesNonnegative division
    (unnormalizedNumerator dataSet n observable)
    (partitionFunction dataSet n)
    (numeratorPositive dataSet n observable nonnegative)
    (finitePartitionNonzero dataSet n)

asScalarCylinderExpectationLimitData :
  ∀ {Observable algebra quotient division} →
  NormalizedCylinderSourceData
    Observable algebra quotient division →
  Cylinder.ScalarCylinderExpectationLimitData
    Observable ℝ algebra
asScalarCylinderExpectationLimitData
    {algebra = algebra} dataSet = record
  { Cylinder.ScalarCylinderExpectationLimitData.zeroObservable =
      zeroObservable dataSet
  ; Cylinder.ScalarCylinderExpectationLimitData.oneObservable =
      oneObservable dataSet
  ; Cylinder.ScalarCylinderExpectationLimitData.addObservable =
      addObservable dataSet
  ; Cylinder.ScalarCylinderExpectationLimitData.scaleObservable =
      scaleObservable dataSet
  ; Cylinder.ScalarCylinderExpectationLimitData.Nonnegative =
      Nonnegative dataSet
  ; Cylinder.ScalarCylinderExpectationLimitData.finiteExpectation =
      finiteNormalized dataSet
  ; Cylinder.ScalarCylinderExpectationLimitData.limitExpectation =
      continuumNormalized dataSet
  ; Cylinder.ScalarCylinderExpectationLimitData.finiteZero =
      finiteNormalizedZero dataSet
  ; Cylinder.ScalarCylinderExpectationLimitData.finiteOne =
      finiteNormalizedOne dataSet
  ; Cylinder.ScalarCylinderExpectationLimitData.finiteAdd =
      finiteNormalizedAdd dataSet
  ; Cylinder.ScalarCylinderExpectationLimitData.finiteScale =
      finiteNormalizedScale dataSet
  ; Cylinder.ScalarCylinderExpectationLimitData.finitePositive =
      finiteNormalizedPositive dataSet
  ; Cylinder.ScalarCylinderExpectationLimitData.selectedConverges =
      normalizedConverges dataSet
  }

normalizedCylinderSourceCompilerLevel : ProofLevel
normalizedCylinderSourceCompilerLevel = machineChecked

realDivisionAlgebraAuthorityLevel : ProofLevel
realDivisionAlgebraAuthorityLevel = standardImported

literalCMP119NumeratorConvergenceLevel : ProofLevel
literalCMP119NumeratorConvergenceLevel = conditional

literalCMP119PartitionConvergenceLevel : ProofLevel
literalCMP119PartitionConvergenceLevel = conditional

literalCMP119PartitionNonzeroLevel : ProofLevel
literalCMP119PartitionNonzeroLevel = conditional
