module DASHI.Foundations.RealElementaryFunctionsCanonicalInstanceExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; 1ℝ ; _+ℝ_ ; _-ℝ_ ; _*ℝ_ ; -ℝ_ ; absℝ ; _≤ℝ_ ; _<ℝ_ )
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Foundations.RealElementaryFunctionsAlternatingSeriesExact as Alt

------------------------------------------------------------------------
-- Canonical elementary functions on DASHI's existing real carrier.
--
-- Marc Daumas, David Lester and César Muñoz,
-- "Verified Real Number Calculations: A Library for Interval Arithmetic",
-- IEEE Transactions on Computers 58 (2009), 226--237.
-- DOI: 10.1109/TC.2008.213; arXiv:0708.3721.
-- Relationship: organization of proof-producing elementary-function bounds.
--
-- Walter Rudin, "Principles of Mathematical Analysis", third edition,
-- McGraw--Hill (1976). No DOI assigned to the book edition used here.
-- Relationship: alternating power series, exponential/logarithm inverse laws
-- and the integral identity for -log(1-u).
--
-- RealAnalysisAxioms intentionally postulates the carrier itself.  Consequently
-- transcendental functions cannot honestly be manufactured by finite Agda
-- definitions below that boundary.  This module fixes ONE canonical extension
-- of that carrier and constructs the shared package consumed by T2--T4.  It does
-- not introduce a second real type or a second incompatible sine convention.
------------------------------------------------------------------------

postulate
  sinℝ cosℝ expℝ logℝ : ℝ → ℝ
  _÷ℝ_ : ℝ → ℝ → ℝ
  powℝ : ℝ → Nat → ℝ
  factorialℝ : Nat → ℝ

  canonicalSinCosAlternatingData :
    Alt.ConfiguredSinCosAlternatingData ℝ

  canonicalNegativeLogOneMinusAuthority :
    Alt.NegativeLogOneMinusAuthority ℝ

  canonicalPositiveExponentialSeriesAuthority :
    Alt.PositiveExponentialSeriesAuthority ℝ

  canonicalLogExpOrderAuthority :
    Alt.LogExpOrderAuthority ℝ

  sineFunctionAgreement :
    Alt.function (Alt.sineSeries canonicalSinCosAlternatingData) ≡ sinℝ

  cosineFunctionAgreement :
    Alt.function (Alt.cosineSeries canonicalSinCosAlternatingData) ≡ cosℝ

  negativeLogFunctionAgreement : Set
  exponentialSeriesFunctionAgreement : Set
  logarithmExponentialFunctionAgreement : Set

repositoryElementaryFunctionPrimitivePackage :
  Alt.ConfiguredElementaryFunctionPrimitivePackage ℝ
repositoryElementaryFunctionPrimitivePackage = record
  { sinCos = canonicalSinCosAlternatingData
  ; negativeLog = canonicalNegativeLogOneMinusAuthority
  ; exponentialSeries = canonicalPositiveExponentialSeriesAuthority
  ; logExp = canonicalLogExpOrderAuthority
  }

repositorySineTermMagnitudeDecreasing =
  Alt.termMagnitudeDecreasing
    (Alt.sineSeries canonicalSinCosAlternatingData)

repositoryCosineTermMagnitudeDecreasing =
  Alt.termMagnitudeDecreasing
    (Alt.cosineSeries canonicalSinCosAlternatingData)

repositorySineFirstOmittedTermBound =
  Alt.firstOmittedTermControlsRemainder
    (Alt.sineSeries canonicalSinCosAlternatingData)

repositoryCosineFirstOmittedTermBound =
  Alt.firstOmittedTermControlsRemainder
    (Alt.cosineSeries canonicalSinCosAlternatingData)

repositoryNegativeLogOneMinusBound =
  Alt.negativeLogOneMinusBound canonicalNegativeLogOneMinusAuthority

repositoryExponentialPartialSumBelow =
  Alt.exponentialPartialSumBelow canonicalPositiveExponentialSeriesAuthority

repositoryLogarithmMonotone =
  Alt.logarithmMonotone canonicalLogExpOrderAuthority

repositoryLogarithmExponential =
  Alt.logarithmExponential canonicalLogExpOrderAuthority

canonicalRealElementaryAdapterLevel : ProofLevel
canonicalRealElementaryAdapterLevel = machineChecked

canonicalRealElementaryFunctionAgreementLevel : ProofLevel
canonicalRealElementaryFunctionAgreementLevel = conditional

repositoryElementaryCalculusAuthorityLevel : ProofLevel
repositoryElementaryCalculusAuthorityLevel = conditional
