{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact where

------------------------------------------------------------------------
-- NORMALIZED EXPECTATION CONVERGENCE
--
-- The YM-specific content is numerator/partition-function convergence.
-- The only external analysis fact used here is ordinary continuity of division
-- away from a nonzero limiting denominator.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record RealQuotientConvergenceAuthority
    (Converges : (Nat → ℝ) → ℝ → Set) : Set₁ where
  field
    divide : ℝ → ℝ → ℝ
    Nonzero : ℝ → Set

    quotientConverges :
      ∀ numerator denominator numeratorLimit denominatorLimit →
      Converges numerator numeratorLimit →
      Converges denominator denominatorLimit →
      Nonzero denominatorLimit →
      Converges
        (λ n → divide (numerator n) (denominator n))
        (divide numeratorLimit denominatorLimit)

open RealQuotientConvergenceAuthority public

record NormalizedExpectationConvergenceData
    (Converges : (Nat → ℝ) → ℝ → Set)
    (authority : RealQuotientConvergenceAuthority Converges)
    (Observable : Set) : Set₁ where
  field
    numerator :
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
        (λ n → numerator n observable)
        (continuumNumerator observable)

    partitionFunctionConverges :
      Converges partitionFunction continuumPartitionFunction

    continuumPartitionFunctionNonzero :
      Nonzero authority continuumPartitionFunction

open NormalizedExpectationConvergenceData public

finiteNormalizedExpectation :
  ∀ {Converges authority Observable} →
  NormalizedExpectationConvergenceData
    Converges authority Observable →
  Nat → Observable → ℝ
finiteNormalizedExpectation {authority = authority} dataSet n observable =
  divide authority
    (numerator dataSet n observable)
    (partitionFunction dataSet n)

continuumNormalizedExpectation :
  ∀ {Converges authority Observable} →
  NormalizedExpectationConvergenceData
    Converges authority Observable →
  Observable → ℝ
continuumNormalizedExpectation {authority = authority} dataSet observable =
  divide authority
    (continuumNumerator dataSet observable)
    (continuumPartitionFunction dataSet)

normalizedExpectationConverges :
  ∀ {Converges authority Observable}
    (dataSet :
      NormalizedExpectationConvergenceData
        Converges authority Observable)
    observable →
  Converges
    (λ n → finiteNormalizedExpectation dataSet n observable)
    (continuumNormalizedExpectation dataSet observable)
normalizedExpectationConverges
    {authority = authority} dataSet observable =
  quotientConverges authority
    (λ n → numerator dataSet n observable)
    (partitionFunction dataSet)
    (continuumNumerator dataSet observable)
    (continuumPartitionFunction dataSet)
    (numeratorConverges dataSet observable)
    (partitionFunctionConverges dataSet)
    (continuumPartitionFunctionNonzero dataSet)

normalizedExpectationConvergenceCompilerLevel : ProofLevel
normalizedExpectationConvergenceCompilerLevel = machineChecked

realQuotientConvergenceAuthorityLevel : ProofLevel
realQuotientConvergenceAuthorityLevel = standardImported

-- These are the actual YM payments consumed by the theorem above.
literalCMP119ObservableNumeratorConvergenceLevel : ProofLevel
literalCMP119ObservableNumeratorConvergenceLevel = conditional

literalCMP119PartitionFunctionConvergenceLevel : ProofLevel
literalCMP119PartitionFunctionConvergenceLevel = conditional

literalCMP119ContinuumPartitionFunctionNonzeroLevel : ProofLevel
literalCMP119ContinuumPartitionFunctionNonzeroLevel = conditional
