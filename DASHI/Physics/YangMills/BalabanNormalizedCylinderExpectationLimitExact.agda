{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact where

------------------------------------------------------------------------
-- UNNORMALIZED CMP119/HAAR LIMITS -> NORMALIZED CYLINDER LIMIT
--
-- This is the exact algebraic bridge needed by literal A.
-- Physics supplies convergence of the unnormalized observable numerators and
-- partition function.  Ordinary real-field quotient laws and quotient
-- continuity then produce the normalized finite expectation sequence.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact as Cylinder

record RealDivisionAlgebra
    (authority :
      Quotient.RealQuotientConvergenceAuthority
        (λ _ _ → Set)) : Set₁ where
  field
    divideZero :
      ∀ denominator →
      Quotient.Nonzero authority denominator →
      Quotient.divide authority 0ℝ denominator ≡ 0ℝ

    divideSelf :
      ∀ denominator →
      Quotient.Nonzero authority denominator →
      Quotient.divide authority denominator denominator ≡ 1ℝ

    divideAddNumerator :
      ∀ left right denominator →
      Quotient.Nonzero authority denominator →
      Quotient.divide authority (left +ℝ right) denominator
      ≡
      Quotient.divide authority left denominator
        +ℝ Quotient.divide authority right denominator

    divideScaleNumerator :
      ∀ scalar numerator denominator →
      Quotient.Nonzero authority denominator →
      Quotient.divide authority (scalar *ℝ numerator) denominator
      ≡
      scalar *ℝ Quotient.divide authority numerator denominator

    dividePreservesNonnegative :
      ∀ numerator denominator →
      0ℝ ≤ℝ numerator →
      Quotient.Nonzero authority denominator →
      0ℝ ≤ℝ Quotient.divide authority numerator denominator

-- The concrete bridge uses an arbitrary standard real convergence relation,
-- but the field algebra above must be stated for the SAME division operation.
record NormalizedCylinderSourceData
    (Observable : Set)
    (Converges : (Nat → ℝ) → ℝ → Set)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority Converges) : Set₁ where
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
      Converges
        (λ n → unnormalizedNumerator n observable)
        (continuumNumerator observable)

    partitionConverges :
      Converges partitionFunction continuumPartitionFunction

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
      unnormalizedNumerator n left +ℝ unnormalizedNumerator n right

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
  ∀ {Observable Converges quotient} →
  NormalizedCylinderSourceData Observable Converges quotient →
  Nat → Observable → ℝ
finiteNormalized {quotient = quotient} dataSet n observable =
  Quotient.divide quotient
    (unnormalizedNumerator dataSet n observable)
    (partitionFunction dataSet n)

continuumNormalized :
  ∀ {Observable Converges quotient} →
  NormalizedCylinderSourceData Observable Converges quotient →
  Observable → ℝ
continuumNormalized {quotient = quotient} dataSet observable =
  Quotient.divide quotient
    (continuumNumerator dataSet observable)
    (continuumPartitionFunction dataSet)

normalizedConverges :
  ∀ {Observable Converges quotient}
    (dataSet :
      NormalizedCylinderSourceData Observable Converges quotient)
    observable →
  Converges
    (λ n → finiteNormalized dataSet n observable)
    (continuumNormalized dataSet observable)
normalizedConverges {quotient = quotient} dataSet observable =
  Quotient.quotientConverges quotient
    (λ n → unnormalizedNumerator dataSet n observable)
    (partitionFunction dataSet)
    (continuumNumerator dataSet observable)
    (continuumPartitionFunction dataSet)
    (numeratorConverges dataSet observable)
    (partitionConverges dataSet)
    (continuumPartitionNonzero dataSet)

normalizedCylinderSourceCompilerLevel : ProofLevel
normalizedCylinderSourceCompilerLevel = machineChecked

realDivisionAlgebraAuthorityLevel : ProofLevel
realDivisionAlgebraAuthorityLevel = standardImported

-- These are now the only YM-specific A-normalization inputs.
literalCMP119NumeratorConvergenceLevel : ProofLevel
literalCMP119NumeratorConvergenceLevel = conditional

literalCMP119PartitionConvergenceLevel : ProofLevel
literalCMP119PartitionConvergenceLevel = conditional

literalCMP119PartitionNonzeroLevel : ProofLevel
literalCMP119PartitionNonzeroLevel = conditional
